// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Functions to generate RISC-V assembly code from a typed Hygge AST in ANF.
module ANFRISCVCodegen

open AST
open RISCV
open Type
open Typechecker


/// Storage information for variables.
[<RequireQualifiedAccess; StructuralComparison; StructuralEquality>]
type internal Storage =
    /// The variable is stored in an integer register.
    | Reg of reg: Reg
    /// The variable is stored in a floating-point register.
    | FPReg of reg: FPReg
    /// This variable is stored on the stack, at the given offset (in bytes)
    /// from the memory address contained in the frame pointer (fp) register.
    | Frame of offset: int


type internal FreeRegisters = {
    Int: List<Reg>
    Float: List<FPReg>
}

/// Code generation environment.
type internal ANFCodegenEnv = {
    /// Target variable for the result of the assembly code execution.
    TargetVar: string
    /// Frame position assigned to each known variable.
    Frame: Map<string, int>
    /// Size of the stack frame.
    FrameSize: int
    /// List of integer variables stored in registers, with newest ones coming
    /// first.  If a variable does not appear here, then it means that it is
    /// allocated on the stack frame.
    IntVarsInRegs: List<string * Reg>
    /// List of float variables stored in registers, with newest ones coming
    /// first. If a float variable does not appear here, then it means that
    /// it is allocated on the stack frame.
    FloatVarsInRegs: List<string * FPReg>
    /// List of available integer registers.
    FreeRegs: FreeRegisters
    /// Set of variables that are needed in the surrounding scope, and should
    /// never be discarded to reuse their storage.
    NeededVars: Set<string>
}


/// Code generation result.
type internal ANFCodegenResult = {
    /// Compiled RISC-V assembly code.
    Asm: Asm
    /// Updated code generation environment.
    Env: ANFCodegenEnv
}


/// Retrieve the name of a variable stored in a 'Var' AST node, and its type.
let internal getVarNameAndType (node: TypedAST): string * Type =
    match node.Expr with
    | Var(vname) -> (vname, expandType node.Env node.Type)
    | _ -> 
        failwith ($"BUG: expecting an AST node with a variable, but got:%s{Util.nl}"
                  + $"%s{PrettyPrinter.prettyPrint node}")


/// Retrieve the name of a variable stored in a 'Var' AST node.
let internal getVarName (node: TypedAST): string =
    fst (getVarNameAndType node)


/// Retrieve the list of variable names stored in a list of 'Var' AST node.
let internal getVarNames (nodes: List<TypedAST>): List<string> =
    List.map getVarName nodes


/// Optionally return the integer register where the given variable is stored
/// within the given codegen environment.
let rec internal findIntVarRegister (env: ANFCodegenEnv) (varName: string) : Option<Reg> =
    match env.IntVarsInRegs with
    | (v, reg) :: _ when v = varName -> Some(reg)
    | _ :: rest -> findIntVarRegister {env with IntVarsInRegs = rest} varName
    | [] -> None
    
    
/// Optionally return the floating-point register where the given variable is
/// stored within the given codegen environment.
let rec internal findFloatVarRegister (env: ANFCodegenEnv) (varName: string) : Option<FPReg> =
    match env.FloatVarsInRegs with
    | (v, fpReg) :: _ when v = varName -> Some(fpReg)
    | _ :: rest -> findFloatVarRegister {env with FloatVarsInRegs = rest} varName
    | [] -> None


/// Get the integer register of 'varName' in the given environment, failing
/// immediately if 'varName' is not loaded in a register.
let internal getIntVarRegister (env: ANFCodegenEnv) (varName: string): Reg =
    (findIntVarRegister env varName).Value


/// Get the floating-point register of 'varName' in the given environment,
/// failing immediately if 'varName' is not loaded in a register.
let internal getFloatVarRegister (env: ANFCodegenEnv) (varName: string): FPReg =
    (findFloatVarRegister env varName).Value


/// Spill the variable with the given name onto its stack position assigned in 'env'.
/// Return the assembly code that performs the spill and the updated codegen environment.
let internal spillVar (env: ANFCodegenEnv) (varName: string): ANFCodegenResult =
    match (findIntVarRegister env varName) with
    | Some(reg) ->
        /// Assembly code to spill the variable
        let spillAsm = Asm(RV.SW(reg, Imm12(env.Frame[varName] * -4), Reg.fp),
                           $"Spill int variable %s{varName} from register %O{reg} to stack")
        /// Variables in registers, after excluding variable being spilled
        let intVarsInRegs2 = List.except [(varName, reg)] env.IntVarsInRegs
        { Asm = spillAsm
          Env = { env with IntVarsInRegs = intVarsInRegs2
                           FreeRegs = { Int = reg :: env.FreeRegs.Int
                                        Float = env.FreeRegs.Float }}}
    | None ->
        match (findFloatVarRegister env varName) with
        | Some(fpReg) ->
            /// Assembly code to spill the float variable
            let spillAsm = Asm(RV.FSW_S(fpReg, Imm12(env.Frame[varName] * -4), Reg.fp),
                               $"Spill float variable %s{varName} from register %O{fpReg} to stack")
            /// Variables in registers, after excluding variable being spilled
            let floatVarsInRegs2 = List.except [(varName, fpReg)] env.FloatVarsInRegs
            { Asm = spillAsm
              Env = { env with FloatVarsInRegs = floatVarsInRegs2
                               FreeRegs.Float = fpReg :: env.FreeRegs.Float }}
            
        | None -> { Env = env; Asm = Asm() } // No need to spill this variable


/// Spill the integer variable that has been stored in an integer register for
/// the longest time, saving it in the stack position assigned in 'env'. Choose
/// a variable that does not belong to the given 'doNotSpill' list. Return the
/// assembly code that performs the spilling, and the updated codegen environment.
let internal spillOldestIntVar (env: ANFCodegenEnv) (doNotSpill: List<string>): ANFCodegenResult =
    /// Variables in registers, starting with the ones allocated earlier
    let varsInRegisters, _ = List.unzip (List.rev env.IntVarsInRegs)
    /// Select the first variable in the given list that is not in 'except'
    let rec selectVar (varRegs: List<string>): string =
        match varRegs with
        | name :: _ when not (List.contains name doNotSpill) -> name
        | _ :: rest -> selectVar rest
        | [] ->
            failwith $"BUG: cannot spill any variable from %O{env.IntVarsInRegs} while excluding %O{doNotSpill}"
    /// Selected variable for spilling
    let selectedVar = selectVar varsInRegisters
    spillVar env selectedVar


/// Spill the oldest float variable that has been stored in a floating-point register
/// for the longest time, saving it in the stack position assigned in 'env'. Choose
/// a variable that does not belong to the given 'doNotSpill' list. Return the
/// assembly code that performs the spilling, and the updated codegen environment.
let internal spillOldestFloatVar (env: ANFCodegenEnv) (doNotSpill: List<string>): ANFCodegenResult =
    /// Variables in registers, starting with the ones allocated earlier
    let varsInRegisters, _ = List.unzip (List.rev env.FloatVarsInRegs)
    /// Select the first variable in the given list that is not in 'except'
    let rec selectVar (varRegs: List<string>): string =
        match varRegs with
        | name :: _ when not (List.contains name doNotSpill) -> name
        | _ :: rest -> selectVar rest
        | [] ->
            failwith $"BUG: cannot spill any variable from %O{env.FloatVarsInRegs} while excluding %O{doNotSpill}"
    /// Selected variable for spilling
    let selectedVar = selectVar varsInRegisters
    spillVar env selectedVar


/// Allocate a position on the stack frame for the given variable, either by using
/// an available position, or by advancing the stack pointer. Return the corresponding
/// codegen result, with the assembly code to update the stack pointer (if needed).
let internal allocateVarOnFrame (env: ANFCodegenEnv) (varName: string): ANFCodegenResult =
    /// Find the lowest unused stack position
    let rec selectFramePos (n: int) =
        if (env.Frame.Values.Contains n) then selectFramePos (n + 1)
        else n
    /// Stack position for the allocated variable
    let stackPos = selectFramePos 0
    /// Assembly code to update the stack pointer, if needed
    let fpUpdateAsm = if stackPos < env.FrameSize then Asm()
                      else Asm(RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)),
                               $"Extend the stack for variable %s{varName}")
    { Asm = fpUpdateAsm
      Env = { env with Frame = env.Frame.Add(varName, stackPos)
                       FrameSize = max (stackPos+1) env.FrameSize } }


/// Allocate a variable that can be stored in an integer register, having the given name,
/// and using the given code generation environment. Return the allocated register, the
/// assembly code needed to allocate that register (if some other variable was spilled
/// on the stack frame), and the corresponding updated code generation environment
/// mapping 'varName' to the allocated register.
let rec internal allocateIntVar (env: ANFCodegenEnv) (varName: string): Reg * ANFCodegenResult =
    /// Codegen result after allocating 'varName' on the frame
    let frameAllocRes = allocateVarOnFrame env varName

    match env.FreeRegs.Int with
    | reg :: rest ->
        /// Updated list of variables in integer registers
        let intVarsInRegs = (varName, reg) :: env.IntVarsInRegs
        (reg, { Asm = frameAllocRes.Asm
                        ++ Asm(RV.COMMENT($"Variable %s{varName} allocation: "
                                          + $"register %O{reg}, "
                                          + $"frame pos. %d{frameAllocRes.Env.Frame[varName]} "))
                Env = {frameAllocRes.Env with FreeRegs.Int = rest
                                              IntVarsInRegs = intVarsInRegs} })
    | [] -> // No free registers available: we spill a variable onto the stack
        /// Assembly code and environment for spilling a variable onto the stack
        let { Asm = spillAsm; Env = spillEnv} = spillOldestIntVar env []
        /// Allocated register, assembly code and environment
        let reg, {Asm = allocAsm; Env = allocEnv} = allocateIntVar spillEnv varName
        (reg, { Asm = spillAsm ++ allocAsm
                Env = allocEnv })


let rec internal allocateFloatVar (env: ANFCodegenEnv) (varName: string): FPReg * ANFCodegenResult =
    /// Codegen result after allocating 'varName' on the frame
    let frameAllocRes = allocateVarOnFrame env varName
    
    match env.FreeRegs.Float with
    | fpReg :: rest ->
        /// Updated list of variables in float registers
        let floatVarsInRegs = (varName, fpReg) :: env.FloatVarsInRegs
        (fpReg, { Asm = frameAllocRes.Asm ++
                        Asm(RV.COMMENT($"Variable %s{varName} allocation: "
                                       + $"FP register %O{fpReg}, "
                                       + $"frame pos. %d{frameAllocRes.Env.Frame[varName]} "))
                  Env = {frameAllocRes.Env with FreeRegs.Float = rest
                                                FloatVarsInRegs = floatVarsInRegs} })
    | [] -> // No free registers available: we spill a variable onto the stack
        /// Assembly code and environment for spilling a float variable onto the stack
        let { Asm = spillAsm; Env = spillEnv} = spillOldestFloatVar env []
        /// Allocated register, assembly code and environment
        let fpReg, {Asm = allocAsm; Env = allocEnv} = allocateFloatVar spillEnv varName
        (fpReg, { Asm = spillAsm ++ allocAsm
                  Env = allocEnv })


/// Load the given variable in the given register.  Return the updated codegen
/// environment.  NOTE: this function assumes that 'varName' is not already
/// loaded in a register, and that 'reg' is a free register.
let internal loadIntVarIntoRegister (env: ANFCodegenEnv) (varName: string)
                                    (reg: Reg): ANFCodegenResult =
    assert List.forall (fun (v, _) -> v <> varName) env.IntVarsInRegs
    assert List.contains reg env.FreeRegs.Int
    /// Remaining free registers after 'varName' is loaded in 'reg'
    let remainingRegs = List.except [reg] env.FreeRegs.Int
    { Asm = Asm(RV.LW(reg, Imm12(env.Frame[varName] * -4), Reg.fp),
                      $"Load variable %s{varName} onto register %O{reg}")
      Env = {env with FreeRegs.Int = remainingRegs
                      IntVarsInRegs = (varName, reg) :: env.IntVarsInRegs} }
    

/// Load the given float variable in the given floating-point register. Return the
/// updated codegen environment. NOTE: this function assumes that 'varName' is not
/// already loaded in a register, and that 'fpReg' is a free floating-point register.
let rec internal loadFloatVarIntoRegister (env: ANFCodegenEnv) (varName: string)
                                          (fpReg: FPReg): ANFCodegenResult =
    assert List.forall (fun (v, _) -> v <> varName) env.FloatVarsInRegs
    assert List.contains fpReg env.FreeRegs.Float
    /// Remaining free floating-point registers after 'varName' is loaded in 'fpReg'
    let remainingFPRegs = List.except [fpReg] env.FreeRegs.Float
    { Asm = Asm(RV.FLW_S(fpReg, Imm12(env.Frame[varName] * -4), Reg.fp),
                      $"Load float variable %s{varName} onto FP register %O{fpReg}")
      Env = {env with FreeRegs.Float = remainingFPRegs
                      FloatVarsInRegs = (varName, fpReg) :: env.FloatVarsInRegs} }


/// Load a non-float variable from the stack frame into an available register,
/// unless the variable is already in a register. If spilling is needed, do not
/// spill any variable in the list 'doNotSpill'. Return the assigned variable
/// register and the loading code and updated codegen environment.
let rec internal loadIntVar (env: ANFCodegenEnv) (varName: string)
                            (doNotSpill: List<string>): Reg * ANFCodegenResult =
    match (findIntVarRegister env varName) with
    | Some(reg) -> (reg, {Asm = Asm(); Env = env})
    | None ->
        match env.FreeRegs.Int with
        | reg :: _ ->
            (reg, loadIntVarIntoRegister env varName reg)
        | [] ->
            /// Assembly code and environment for spilling a variable onto the stack
            let { Asm = spillAsm; Env = spillEnv} = spillOldestIntVar env doNotSpill
            /// Register and codegen env after variable spilling and loading
            let reg, loadCodegenRes = loadIntVar spillEnv varName doNotSpill
            (reg, { Asm = spillAsm ++ loadCodegenRes.Asm
                    Env = loadCodegenRes.Env })


/// Load a float variable from the stack frame into an available floating-point register,
/// unless the variable is already in a register. If spilling is needed, do not spill any
/// variable in the list 'doNotSpill'. Return the assigned variable register and the
/// loading code and updated codegen environment.
let rec internal loadFloatVar (env: ANFCodegenEnv) (varName: string)
                              (doNotSpill: List<string>): FPReg * ANFCodegenResult =
    match (findFloatVarRegister env varName) with
    | Some(fpReg) -> (fpReg, {Asm = Asm(); Env = env})
    | None ->
        match env.FreeRegs.Float with
        | fpReg :: _ ->
            let loadRes = loadFloatVarIntoRegister env varName fpReg
            (fpReg, loadRes)
        | [] ->
            /// Assembly code and environment for spilling a variable onto the stack
            let spillRes = spillOldestFloatVar env doNotSpill
            /// Register and codegen env after variable spilling and loading
            let fpReg, loadCodegenRes = loadFloatVar spillRes.Env varName doNotSpill
            (fpReg, { Asm = spillRes.Asm ++ loadCodegenRes.Asm
                      Env = loadCodegenRes.Env })


/// Take a codegen environment and list of variable names, and load each
/// variable in a register.  If spilling is needed, do not spill any variable in
/// the list 'doNotSpill'.  Return the list of registers containing the
/// variables, and the updated codegen environment after loading the variables.
let internal loadVars (env: ANFCodegenEnv)
                      (vars: List<TypedAST>)
                      (doNotSpill: List<string>): List<Reg> * List<FPReg> * ANFCodegenResult =
    /// List of variable names and types in the 'vars' AST nodes
    let varNamesTypes = List.map getVarNameAndType vars
    /// List of variable names in the 'vars' AST nodes
    let varNames = getVarNames vars

    /// Folder function that accumulates the codegen to load variables
    let loader (regs: List<Reg>, fpRegs: List<FPReg>, codegenRes: ANFCodegenResult) (vname, tpe) =
        match tpe with
        | TFloat ->
            /// Register and codegen result after loading variable vname. When loading
            /// the variable, we ensure that none of the variables in 'vars' is spilled
            let fpReg, loadRes = loadFloatVar codegenRes.Env vname (doNotSpill @ varNames)
            (regs, fpRegs @ [fpReg], {codegenRes with Env = loadRes.Env
                                                      Asm = codegenRes.Asm ++ loadRes.Asm})
        | _ -> // int-like variables are included
            /// Register and codegen result after loading variable 'vname'. When loading
            /// the variable, we ensure that none of the variables in 'vars' is spilled
            let reg, loadRes = loadIntVar codegenRes.Env vname (doNotSpill @ varNames)
            (regs @ [reg], fpRegs, {codegenRes with Env = loadRes.Env
                                                    Asm = codegenRes.Asm ++ loadRes.Asm})

    List.fold loader ([], [], {Asm = Asm(); Env = env}) varNamesTypes


/// Make available more registers in the given codegen environment, by removing
/// all variables that are neither in the given set of needed variables, nor in
/// env.NeededVars, nor env.TargetVar. Return an updated code generation environment.
let internal cleanupUnusedVars (env: ANFCodegenEnv) (neededVars: Set<string>): ANFCodegenEnv =
    /// Set of all needed variables that cannot be removed from storage
    let needed = (Set.union neededVars env.NeededVars).Add(env.TargetVar)
    /// Cleaned-up frame with unnecessary variables removed
    let cleanFrame = Map.filter (fun v _-> needed.Contains v) env.Frame
    /// Cleaned-up list of variables in int registers
    let intVarsInRegs = List.filter (fun (v,_)-> needed.Contains v) env.IntVarsInRegs
    /// Cleaned-up list of variables in float registers
    let floatVarsInRegs = List.filter (fun (v,_)-> needed.Contains v) env.FloatVarsInRegs
    /// Folder function to collect all deallocated integer registers
    let deallocIntRegs (acc: List<Reg>) (varName: string, reg: Reg) =
        if not (needed.Contains varName) then reg :: acc else acc
    /// List of deallocated integer registers
    let deallocatedRegs = List.fold deallocIntRegs [] env.IntVarsInRegs
    /// Folder function to collect all deallocated float registers
    let deallocFloatRegs (acc: List<FPReg>) (varName: string, fpReg: FPReg) =
        if not (needed.Contains varName) then fpReg :: acc else acc
    /// List of deallocated float registers
    let deallocatedFloatRegs = List.fold deallocFloatRegs [] env.FloatVarsInRegs
    /// List of free registers after the deallocation
    let freeRegs = { Int = deallocatedRegs @ env.FreeRegs.Int
                     Float = deallocatedFloatRegs @ env.FreeRegs.Float }

    { env with Frame = cleanFrame
               IntVarsInRegs = intVarsInRegs
               FloatVarsInRegs = floatVarsInRegs
               FreeRegs = freeRegs }


/// Generate assembly code that spills/loads variables in 'fromEnv' achieving
/// the same configuration of 'toEnv'.
let internal syncANFCodegenEnvs (fromEnv: ANFCodegenEnv)
                                (toEnv: ANFCodegenEnv): Asm =
    assert(fromEnv.NeededVars = toEnv.NeededVars)

    // Cleanup unused variables in the environments
    let fromEnv = cleanupUnusedVars fromEnv Set[]
    let toEnv = cleanupUnusedVars toEnv Set[]

    assert(fromEnv.Frame = toEnv.Frame)

    // Variables loaded in a register in 'fromEnv'
    let fromIntVarsInRegs = Set.ofList (fst (List.unzip fromEnv.IntVarsInRegs))
    let fromFloatVarsInRegs = Set.ofList (fst (List.unzip fromEnv.FloatVarsInRegs))
    let fromVarsInRegs = Set.union fromIntVarsInRegs fromFloatVarsInRegs
    
    // Variables loaded in a register in 'toEnv'
    let toIntVarsInRegs = Set.ofList (fst (List.unzip toEnv.IntVarsInRegs))
    let toFloatVarsInRegs = Set.ofList (fst (List.unzip toEnv.FloatVarsInRegs))
    let toVarsInRegs = Set.union toIntVarsInRegs toFloatVarsInRegs

    /// Variables loaded in a register in 'toEnv' but not in 'fromEnv'
    let varsToLoad = Set.filter (fun v -> not (fromVarsInRegs.Contains v))
                                toVarsInRegs
    /// Variables loaded in a register in 'fromEnv' but not in 'toEnv'
    let varsToSpill = Set.filter (fun v -> not (toVarsInRegs.Contains v))
                                 fromVarsInRegs
    /// Is 'varName' loaded in different registers in 'fromEnv' and 'toEnv'?
    let needsReload (varName: string): bool =
        /// Identify the variable names loaded in registers in both environments
        let consistentIntVarNames = Set.intersect fromIntVarsInRegs toIntVarsInRegs
        let consistentFloatVarNames = Set.intersect fromFloatVarsInRegs toFloatVarsInRegs
        
        let intNeedsReload = (consistentIntVarNames.Contains varName &&
            (getIntVarRegister fromEnv varName) <> (getIntVarRegister toEnv varName))
        let floatNeedsReload = (consistentFloatVarNames.Contains varName &&
         (getFloatVarRegister fromEnv varName) <> (getFloatVarRegister toEnv varName))
         
        intNeedsReload || floatNeedsReload

    /// Variables loaded in different registers in 'fromEnv' and 'toEnv'
    let varsToReload = Set.filter needsReload toVarsInRegs

    /// Folder function that accumulates code to spill variables
    let spiller (codegenRes: ANFCodegenResult) (varName: string) =
        /// Variable spilling codegen result
        let spillRes = spillVar codegenRes.Env varName
        { codegenRes with Env = spillRes.Env
                          Asm = codegenRes.Asm ++ spillRes.Asm }

    /// Folder function that accumulates code to load variables
    let loader (codegenRes: ANFCodegenResult) (varName: string) =
        /// Variable loading codegen result
        let loadRes = loadIntVarIntoRegister codegenRes.Env varName
                                             (getIntVarRegister toEnv varName)
        { codegenRes with Env = loadRes.Env
                          Asm = codegenRes.Asm ++ loadRes.Asm }

    /// Code generation result for spilling variables
    let spillRes = Set.fold spiller {Asm = Asm(); Env = fromEnv}
                            (Set.union varsToSpill varsToReload)
    /// Code generation result for loading variables
    let loadRes = Set.fold loader spillRes (Set.union varsToLoad varsToReload)

    assert(loadRes.Env.Frame = toEnv.Frame)
    assert((Set.ofList loadRes.Env.IntVarsInRegs) = (Set.ofList toEnv.IntVarsInRegs))

    loadRes.Asm


let prebindPrintTarget (printNodes: List<TypedAST>): List<TypedAST> =
    let folder (acc:List<TypedAST>) (elem: TypedAST): List<TypedAST> =
        /// Generated unique variable name for each print operation
        let printVarName = Util.genSymbol "$prnt"
        let unitVarName = Util.genSymbol "$ignr"
        
        let printout = { elem with Expr = Print({ elem with Expr = Var(printVarName) }); Type = TUnit }
        let preBind = { elem with Expr =
                                    Let(printVarName, elem,
                                        { elem with Expr =
                                                    Let(unitVarName, printout,
                                                        { elem with Expr = Var(unitVarName); Type = TUnit })
                                        })
                      }
        acc @ [preBind]
    List.fold folder [] printNodes


/// Code generation function: compile the expression in the given AST node,
/// which is expected to be in ANF.
let rec internal doCodegen (env: ANFCodegenEnv)
                           (node: TypedAST): ANFCodegenResult =
    match node.Expr with
    | Var(vname) when (expandType node.Env node.Type) <> TFloat ->
        /// Target register to store the vname's value, and code to load it
        let targetReg, targetLoadRes = loadIntVar env env.TargetVar [vname]
        match findIntVarRegister targetLoadRes.Env vname with
        | Some(reg) ->
            { Env = targetLoadRes.Env
              Asm = targetLoadRes.Asm
                        ++ Asm(RV.MV(targetReg, reg),
                                     $"%s{env.TargetVar} <- %s{vname}") }
        | None ->
            { Env = targetLoadRes.Env
              Asm = targetLoadRes.Asm
                        ++ Asm(RV.LW(targetReg, Imm12(env.Frame[vname] * -4), Reg.fp),
                               $"%s{env.TargetVar} <- %s{vname}") }
    | Var(vname) when (expandType node.Env node.Type) = TFloat ->
        /// Target floating-point register to store the vname's value, and code to load it
        let targetFPReg, targetLoadRes = loadFloatVar env env.TargetVar [vname]
        match findFloatVarRegister targetLoadRes.Env vname with
        | Some(fpReg) ->
            { Env = targetLoadRes.Env
              Asm = targetLoadRes.Asm
                        ++ Asm(RV.FMV_S(targetFPReg, fpReg),
                                     $"%s{env.TargetVar} <- %s{vname}") }
        | None ->
            { Env = targetLoadRes.Env
              Asm = targetLoadRes.Asm
                        ++ Asm(RV.FLW_S(targetFPReg, Imm12(env.Frame[vname] * -4), Reg.fp),
                               $"%s{env.TargetVar} <- %s{vname}") }

    | Let(vname, init, scope)
    | LetT(vname, _, init, scope) ->
        /// Cleaned-up codegen environment reduced to the variables that are
        /// actually used in the 'let' init and scope
        let initEnv = cleanupUnusedVars env (Set.union (ASTUtil.freeVars init)
                                                       (ASTUtil.freeVars scope))
        /// Code generation for the 'init' expression
        let initRes =
            match (expandType init.Env init.Type) with
            | t when t <> TFloat ->
                /// Allocation code for 'vname' + updated codegen environment
                let _, allocRes = allocateIntVar initEnv vname
                /// Code generation environment for the init block of the 'let',
                /// where all variables used in the 'scope' are marked as
                /// 'needed' (since they must not be deallocated, although they
                /// may not be used in the 'init' expression itself)
                let initCodegenEnv =
                    { allocRes.Env with TargetVar = vname
                                        NeededVars = Set.union env.NeededVars
                                                               (ASTUtil.freeVars scope) }
                /// Code generation result for 'init' expression
                let initCodegenRes = doLetInitCodegen initCodegenEnv init
                { initCodegenRes with Asm = allocRes.Asm ++ initCodegenRes.Asm }
            | TFloat ->
                /// Allocation code for 'vname' + updated codegen environment
                let _, allocRes = allocateFloatVar initEnv vname
                /// Code generation environment for the init block of the 'let',
                /// where all variables used in the 'scope' are marked as
                /// 'needed' (since they must not be deallocated, although they
                /// may not be used in the 'init' expression itself)
                let initCodegenEnv =
                    { allocRes.Env with TargetVar = vname
                                        NeededVars = Set.union env.NeededVars
                                                               (ASTUtil.freeVars scope) }
                /// Code generation result for 'init' expression
                let initCodegenRes = doLetInitCodegen initCodegenEnv init
                { initCodegenRes with Asm = allocRes.Asm ++ initCodegenRes.Asm }
                
            | t -> failwith $"BUG: unsupported init expression type %O{t}"
        /// Cleaned-up codegen environment reduced to the variables that are
        /// actually used in the 'let' scope
        let scopeEnv =
            cleanupUnusedVars {initRes.Env with NeededVars = env.NeededVars
                                                TargetVar = env.TargetVar }
                              (ASTUtil.freeVars scope)
        /// Code generation for the 'let' scope assumed in ANF
        let scopeCodegenResult = doCodegen scopeEnv scope
        { Asm = initRes.Asm ++ scopeCodegenResult.Asm
          Env = scopeCodegenResult.Env }


    | LetRec(name, _, init, scope)
    | LetMut(name, init, scope) ->
        // The code generation is the same as 'let...', so we recycle it
        doCodegen env {node with Expr = Let(name, init, scope)}

    | _ ->
        failwith ($"BUG: unsupported AST node for 'let' scope, maybe not in ANF:%s{Util.nl}"
                  + $"%s{PrettyPrinter.prettyPrint node}")

/// Code generation for an expression that appears in the 'init' block of a
/// 'let' binder, and should save its result in the 'target' register in the
/// environment.  The expression is expected to be in ANF.
and internal doLetInitCodegen (env: ANFCodegenEnv) (init: TypedAST): ANFCodegenResult =
    match init.Expr with
    | Var vname ->
        /// Register containing the source variable value and ANF code to load it (if necessary)
        let sourceReg, loadRes = loadIntVar env vname []
        /// Register holding the target and ANF codegen result to load it
        let targetReg, targetLoadRes = loadIntVar env env.TargetVar [vname]
        
        /// Assembly code to load the source value into the target
        let moveCode = Asm(RV.MV(targetReg, sourceReg), $"Copy: {vname} <- {env.TargetVar}")
        
        { Asm = loadRes.Asm ++ targetLoadRes.Asm ++ moveCode
          Env = targetLoadRes.Env }

    | UnitVal -> { Asm = Asm() // Nothing to do
                   Env = env }

    | StringVal(v) ->
        /// Label marking the string constant in the data segment
        let label = Util.genSymbol "string_val"
        /// Target register to store the string value and code to load it
        let targetReg, targetLoadRes = loadIntVar env env.TargetVar []
        /// Code for storing the string at label, and loading its address
        let strAddressCode = Asm()
                                 .AddData(label, Alloc.String(v))
                                 .AddText(RV.LA(targetReg, label))
        { Asm = targetLoadRes.Asm ++ strAddressCode
          Env = targetLoadRes.Env }

    | BoolVal(value) ->
        /// Target register to store the boolean value and code to load it
        let targetReg, targetLoadRes = loadIntVar env env.TargetVar []
        { Asm = targetLoadRes.Asm ++ Asm(RV.LI(targetReg,
                                               if value then 1 else 0))
          Env = targetLoadRes.Env }

    | IntVal(value) ->
        /// Target register to store the integer value and code to load it
        let targetReg, targetLoadRes = loadIntVar env env.TargetVar []
        { Asm = targetLoadRes.Asm ++ Asm(RV.LI(targetReg, value))
          Env = targetLoadRes.Env }
        
    | FloatVal(v) ->
        // We convert the float value into its bytes, and load it as immediate
        let bytes = System.BitConverter.GetBytes(v)
        if (not System.BitConverter.IsLittleEndian)
            then System.Array.Reverse(bytes) // RISC-V is little-endian
        let word: int32 = System.BitConverter.ToInt32(bytes)
        
        /// Temporary int register used for loading (alternate link register - needs to restore)
        let tempReg = Reg.t0
        
        /// Target register to store the float value and code to load it
        let targetReg, targetLoadRes = loadFloatVar env env.TargetVar []
        
        // Current handling of floats writes bytes to t0 then to fpreg, but we use t0 to store the function address.
        // Solution: We save the contents of the env.Target register before using it to perform the conversion, then it is restored after the float val is loaded into FP reg.
        let floatLoadingCode = Asm([
              (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space to save register") // RARS commenting for debugging... if it's annoying you can remove it.
              (RV.SW(tempReg, Imm12(0), Reg.sp), "Save t0 (temp) register to stack")
              (RV.LI(tempReg, word), $"Float value %f{v}")
              (RV.FMV_W_X(targetReg, tempReg), $"Move float value %f{v} to FP register")
              (RV.LW(tempReg, Imm12(0), Reg.sp), "Restore t0 (temp) register from stack")
              (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")
        ])
        
        { Asm = targetLoadRes.Asm ++ floatLoadingCode
          Env = targetLoadRes.Env }
        

    | Add(lhs, rhs)
    | Sub(lhs, rhs)
    | Div(lhs, rhs)
    | Mod(lhs, rhs)
    | Min(lhs, rhs)
    | Max(lhs, rhs)
    | Mult(lhs, rhs) as expr ->
        /// Names of the variables used by the lhs and rhs of this operation
        let lrVarNames = getVarNames [lhs; rhs]
        match (loadVars env [lhs; rhs] []) with
        | [lhsReg; rhsReg], [], argLoadRes
            when isSubtypeOf init.Env init.Type TInt ->
            /// Target register to store the operation result + code to load it
            let targetReg, targetLoadRes =
                loadIntVar argLoadRes.Env env.TargetVar lrVarNames
            let label = Util.genSymbol "minmax_exit"
            /// Assembly code for the operation
            let opAsm =
                match expr with
                | Add _ -> Asm(RV.ADD(targetReg, lhsReg, rhsReg),
                                  $"%s{env.TargetVar} <- %s{lrVarNames[0]} + %s{lrVarNames[1]}")
                | Sub _ -> Asm(RV.SUB(targetReg, lhsReg, rhsReg),
                                  $"%s{env.TargetVar} <- %s{lrVarNames[0]} - %s{lrVarNames[1]}")
                | Mult _ -> Asm(RV.MUL(targetReg, lhsReg, rhsReg),
                                   $"%s{env.TargetVar} <- %s{lrVarNames[0]} * %s{lrVarNames[1]}")
                | Div _ -> Asm(RV.DIV(targetReg, lhsReg, rhsReg),
                                   $"%s{env.TargetVar} <- %s{lrVarNames[0]} / %s{lrVarNames[1]}")
                | Mod _ -> Asm(RV.REM(targetReg, lhsReg, rhsReg),
                                   $"%s{env.TargetVar} <- %s{lrVarNames[0]} %% %s{lrVarNames[1]}")
                | Min _ -> Asm().AddText([
                        (RV.BLT(targetReg, rhsReg, label), $"%s{env.TargetVar} <- min(%s{lrVarNames[0]}, %s{lrVarNames[1]})")
                        (RV.MV(targetReg, rhsReg), "")
                        (RV.LABEL(label), "")
                    ])
                | Max _ -> Asm().AddText([
                        (RV.BLT(rhsReg, targetReg, label), $"%s{env.TargetVar} <- max(%s{lrVarNames[0]}, %s{lrVarNames[1]})")
                        (RV.MV(targetReg, rhsReg), "")
                        (RV.LABEL(label), "")
                    ])
                | x -> failwith $"BUG: unexpected binary arithmetic operation %O{x}"
            { Asm = argLoadRes.Asm ++ targetLoadRes.Asm ++ opAsm
              Env = targetLoadRes.Env }
        | [], [lhsFpReg; rhsFpReg], argLoadRes
            when isSubtypeOf init.Env init.Type TFloat ->
            /// Target floating-point register to store the operation result + code to load it
            let targetFPReg, targetLoadRes =
                loadFloatVar argLoadRes.Env env.TargetVar lrVarNames
            let labelChoice = Util.genSymbol "minmax_choice"
            let labelExit = Util.genSymbol "minmax_exit"
            /// Temporary register
            let tempReg = Reg.t0
            /// Assembly code for the floating-point operation
            let opAsm =
                match expr with
                | Add _ ->
                    Asm(RV.FADD_S(targetFPReg, lhsFpReg, rhsFpReg),
                         $"%s{env.TargetVar} <- %s{lrVarNames[0]} + %s{lrVarNames[1]}")
                | Sub _ ->
                    Asm(RV.FSUB_S(targetFPReg, lhsFpReg, rhsFpReg),
                         $"%s{env.TargetVar} <- %s{lrVarNames[0]} - %s{lrVarNames[1]}")
                | Mult _ ->
                    Asm(RV.FMUL_S(targetFPReg, lhsFpReg, rhsFpReg),
                         $"%s{env.TargetVar} <- %s{lrVarNames[0]} * %s{lrVarNames[1]}")
                | Div _ ->
                    Asm(RV.FDIV_S(targetFPReg, lhsFpReg, rhsFpReg),
                         $"%s{env.TargetVar} <- %s{lrVarNames[0]} / %s{lrVarNames[1]}")
                | Mod _ ->
                    failwith "BUG: remainder operation on floats is not supported"
                | Min _ ->
                    Asm([
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space to save register") // RARS commenting for debugging... if it's annoying you can remove it.
                        (RV.SW(tempReg, Imm12(0), Reg.sp), "Save t0 (temp) register to stack")
                        (RV.FLT_S(tempReg, rhsFpReg, lhsFpReg), "Compare the float arguments")
                        (RV.BEQ(tempReg, Reg.zero, labelChoice), "")
                        (RV.FMV_S(targetFPReg, rhsFpReg), "Take rhs argument as the minimum")
                        (RV.J(labelExit), "")
                        (RV.LABEL(labelChoice), "")
                        (RV.FMV_S(targetFPReg, lhsFpReg), "Take lhs argument as the minimum")
                        (RV.LABEL(labelExit), $"%s{env.TargetVar} <- min(%s{lrVarNames[0]}, %s{lrVarNames[1]})")
                        (RV.LW(tempReg, Imm12(0), Reg.sp), "Restore t0 (temp) register from stack")
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")                        
                    ])
                | Max _ ->
                    Asm([
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space to save register") // RARS commenting for debugging... if it's annoying you can remove it.
                        (RV.SW(tempReg, Imm12(0), Reg.sp), "Save t0 (temp) register to stack")
                        (RV.FLT_S(tempReg, lhsFpReg, rhsFpReg), "Compare the float arguments")
                        (RV.BEQ(tempReg, Reg.zero, labelChoice), "")
                        (RV.FMV_S(targetFPReg, rhsFpReg), "Take rhs argument as the maximum")
                        (RV.J(labelExit), "")
                        (RV.LABEL(labelChoice), "")
                        (RV.FMV_S(targetFPReg, lhsFpReg), "Take lhs argument as the minimum")                        
                        (RV.LABEL(labelExit), $"%s{env.TargetVar} <- max(%s{lrVarNames[0]}, %s{lrVarNames[1]})")
                        (RV.LW(tempReg, Imm12(0), Reg.sp), "Restore t0 (temp) register from stack")
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")                        
                    ])
                | x -> failwith $"BUG: unexpected binary arithmetic operation %O{x}"
                    
            { Asm = argLoadRes.Asm ++ targetLoadRes.Asm ++ opAsm
              Env = targetLoadRes.Env }
            
        | x ->
            failwith $"BUG: unexpected return value from 'loadVars': %O{x}"
    
    | Sqrt(arg) ->
        /// Name of the argument variable for the operation
        let argVarName = getVarName arg
        match arg.Type with
        | TFloat ->
            /// Register of the loaded float-argument variable, and code to load it
            let argFpReg, argLoadRes = loadFloatVar env argVarName []
            
            /// Target register to store the operation result + code to load it
            let targetFpReg, targetLoadRes =
                loadFloatVar argLoadRes.Env env.TargetVar [argVarName]
                
            /// Assembly code for the square root operation
            let sqrtCode = Asm(RV.FSQRT_S(targetFpReg, argFpReg), $"%s{env.TargetVar} <- sqrt(%s{argVarName})")
            
            { Asm = argLoadRes.Asm ++ targetLoadRes.Asm ++ sqrtCode
              Env = targetLoadRes.Env }
        | TInt ->
            /// Register of the loaded argument variable, and code to load it
            let argReg, argLoadRes = loadIntVar env argVarName []
            
            /// Target register to store the operation result + code to load it
            let targetFpReg, targetLoadRes =
                loadFloatVar argLoadRes.Env env.TargetVar [argVarName]
                
            /// Assembly code for the square root operation
            let sqrtCode = Asm([
                (RV.FCVT_S_W(targetFpReg, argReg), "Convert sqrt-argument to float")
                (RV.FSQRT_S(targetFpReg, targetFpReg), $"%s{env.TargetVar} <- sqrt(%s{argVarName})")
            ])
            { Asm = argLoadRes.Asm ++ targetLoadRes.Asm ++ sqrtCode
              Env = targetLoadRes.Env }
        | _ -> failwith "BUG: Sqrt codegen invoked on unsupported type %O{arg.Type}"

    | Eq(lhs, rhs)
    | Less(lhs, rhs)
    | LessEq(lhs, rhs)
    | Greater(lhs, rhs)
    | GreaterEq(lhs, rhs) as expr ->
        /// Names of the variables used by the lhs and rhs of this operation
        let lrVarNames = getVarNames [lhs; rhs]
        /// Human-readable prefix for jump labels, describing the kind of
        /// relational operation we are compiling
        let labelName = match expr with
                        | Eq _ -> "eq"
                        | Less _ -> "less"
                        | LessEq _ -> "less_eq"
                        | Greater _ -> "greater"
                        | GreaterEq _ -> "greater_eq"
                        | x -> failwith $"BUG: unexpected operation %O{x}"

        match (loadVars env [lhs; rhs] []) with
        | [lhsReg; rhsReg], [], argLoadRes
            when (expandType lhs.Env lhs.Type) = TInt  ->
            /// Target register to store the operation result + code to load it
            let targetReg, targetLoadRes = loadIntVar argLoadRes.Env env.TargetVar lrVarNames
            /// Label to jump to when the comparison is true
            let trueLabel = Util.genSymbol $"%O{labelName}_true"
            /// Label to mark the end of the comparison code
            let endLabel = Util.genSymbol $"%O{labelName}_end"

            /// Codegen for the relational operation between lhs and rhs
            let opAsm =
                match expr with
                | Eq _ ->
                    Asm(RV.BEQ(lhsReg, rhsReg, trueLabel))
                | Less _ ->
                    Asm(RV.BLT(lhsReg, rhsReg, trueLabel))
                | LessEq _ ->
                    Asm(RV.BLE(lhsReg, rhsReg, trueLabel))
                | Greater _ ->
                    Asm(RV.BGT(lhsReg, rhsReg, trueLabel))
                | GreaterEq _ ->
                    Asm(RV.BGE(lhsReg, rhsReg, trueLabel))
                | x -> failwith $"BUG: unexpected operation %O{x}"

            /// Generated code where we put everything
            let asm = (argLoadRes.Asm ++ targetLoadRes.Asm ++ opAsm)
                        .AddText([
                            (RV.LI(targetReg, 0), "Comparison result is false")
                            (RV.J(endLabel), "")
                            (RV.LABEL(trueLabel), "")
                            (RV.LI(targetReg, 1), "Comparison result is true")
                            (RV.LABEL(endLabel), "")
                        ])
            { Asm = asm
              Env = targetLoadRes.Env }
        | regs, fpRegs, argLoadRes
            when not fpRegs.IsEmpty && (expandType lhs.Env lhs.Type) = TFloat ->
            /// Target register to store the operation result + code to load it
            let targetReg, targetLoadRes = loadIntVar argLoadRes.Env env.TargetVar lrVarNames
            
            let lhsFpReg = fpRegs.Head
            let rhsFpReg, rhsFLoadRes =
                match regs with 
                | [_] ->
                    let rhsFpReg, rhsConvRes = loadFloatVar argLoadRes.Env $"{lrVarNames[1]}_f" [lrVarNames.Head]
                    rhsFpReg, rhsConvRes
                | _ -> fpRegs[1], { Asm = Asm(); Env = targetLoadRes.Env }
            
            /// Codegen to convert the rhs argument to a float, if needed (support typer for increment/decrement)
            let rhsConv = match regs with
                          | [rhsReg] ->
                              { Asm = rhsFLoadRes.Asm ++
                                      Asm(RV.FCVT_S_W(rhsFpReg, rhsReg), "Convert rhs integer argument to float")
                                Env = rhsFLoadRes.Env }
                          | _ -> rhsFLoadRes
            
            /// Codegen for the relational operation between lhs and rhs
            let opAsm =
                match expr with
                | Eq _ ->
                    Asm(RV.FEQ_S(targetReg, lhsFpReg, rhsFpReg))
                | Less _ ->
                    Asm(RV.FLT_S(targetReg, lhsFpReg, rhsFpReg))
                | LessEq _ ->
                    Asm(RV.FLE_S(targetReg, lhsFpReg, rhsFpReg))
                | Greater _ ->
                    Asm(RV.FGT_S(targetReg, lhsFpReg, rhsFpReg))
                | GreaterEq _ ->
                    Asm(RV.FGE_S(targetReg, lhsFpReg, rhsFpReg))
                | x -> failwith $"BUG: unexpected operation %O{x}"
            { Asm = argLoadRes.Asm ++ targetLoadRes.Asm ++ rhsConv.Asm ++ opAsm
              Env = rhsConv.Env }
        | x ->
            failwith ($"BUG: unexpected return value from 'loadVars': %O{x}."
                   + $"Potentially, different types of arguments %O{lhs.Type} and %O{rhs.Type} in relational operation %O{expr}")
    
    | And(lhs, rhs)
    | Or(lhs, rhs) as expr ->
        // Code generation for logical 'and' and 'or' is very similar: we
        // compile the lhs and rhs giving them different target registers, and
        // then apply the relevant assembly operation(s) on their results.
        
        /// Generated code for lhs expression
        let lhsReg, lhsLoadRes = loadIntVar env (getVarName lhs) []
        /// Generated code for rhs expression
        let rhsReg, rhsLoadRes = loadIntVar lhsLoadRes.Env (getVarName rhs) [getVarName lhs]
        
        /// Target register to store the operation result + code to load it
        let targetReg, targetLoadRes =
            loadIntVar rhsLoadRes.Env env.TargetVar [getVarName lhs; getVarName rhs]
        
        /// Generated assembly code for the operation
        let opAsm =
            match expr with
            | And _ ->
                Asm(RV.AND(targetReg, lhsReg, rhsReg),
                     $"%s{env.TargetVar} <- %s{getVarName lhs} and %s{getVarName rhs}")
            | Or _ ->
                Asm(RV.OR(targetReg, lhsReg, rhsReg),
                     $"%s{env.TargetVar} <- %s{getVarName lhs} or %s{getVarName rhs}")
            | x -> failwith $"BUG: unexpected operation %O{x}"

        { Asm = lhsLoadRes.Asm ++ rhsLoadRes.Asm ++ targetLoadRes.Asm ++ opAsm
          Env = targetLoadRes.Env }
    
    | Not(arg) ->
        /// Generated code and register loading the argument
        let argReg, argLoadRes = loadIntVar env (getVarName arg) []
        /// Target register to store the operation result + code to load it
        let targetReg, targetLoadRes = loadIntVar argLoadRes.Env env.TargetVar [getVarName arg]
        { Env = targetLoadRes.Env
          Asm = argLoadRes.Asm ++ targetLoadRes.Asm
                ++ Asm(RV.SEQZ(targetReg, argReg), $"%s{env.TargetVar} <- not %s{getVarName arg}") }
    
    | ReadInt ->
        /// Target register to store the read integer value + code to load it
        let targetReg, targetLoadRes = loadIntVar env env.TargetVar []
        let readCode =
            (beforeSysCall [Reg.a0] []) ++
            Asm([
                (RV.LI(Reg.a7, 5), "RARS syscall: ReadInt")
                (RV.ECALL, "")
                (RV.MV(targetReg, Reg.a0), "Move syscall result to target")
            ])
            ++ (afterSysCall [Reg.a0] [])
        { Asm = targetLoadRes.Asm ++ readCode
          Env = targetLoadRes.Env }
    | ReadFloat ->
        /// Target register to store the read float value + code to load it
        let targetFPReg, targetLoadRes = loadFloatVar env env.TargetVar []
        let readCode =
            (beforeSysCall [Reg.a0] []) ++
            Asm([
                (RV.LI(Reg.a7, 6), "RARS syscall: ReadFloat")
                (RV.ECALL, "")
                (RV.FMV_W_X(targetFPReg, Reg.a0), "Move syscall result to target")
            ])
            ++ (afterSysCall [Reg.a0] [])
        { Asm = targetLoadRes.Asm ++ readCode
          Env = targetLoadRes.Env }

    | Print(arg) when (expandType arg.Env arg.Type) = TFloat ->
        /// Register holding printing argument, and code to load it
        let argFpReg, argLoadRes = loadFloatVar env (getVarName arg) []
        
        /// Printout code for integer variables
        let floatPrintCode = (beforeSysCall [] [FPReg.fa0])
                                 .AddText([
                                     (RV.FMV_S(FPReg.fa0, argFpReg), "Copy to fa0 for printing")
                                     (RV.LI(Reg.a7, 2), "RARS syscall: PrintFloat")
                                     (RV.ECALL, "")
                                 ])
                             ++ (afterSysCall [] [FPReg.fa0])
        { Asm = argLoadRes.Asm ++ floatPrintCode
          Env = argLoadRes.Env }
    | Print(arg) ->
        /// Register holding printing argument, and code to load it
        let argVarName = getVarName arg
        let argReg, argLoadRes = loadIntVar env argVarName []
        // The generated code depends on the `print` argument type
        match expandType arg.Env arg.Type with
        | TBool ->
            let strTrue = Util.genSymbol "true"
            let strFalse = Util.genSymbol "false"
            let printFalse = Util.genSymbol "print_false"
            let printExec = Util.genSymbol "print_execute"
            /// Printout code for boolean variables
            let boolPrintCode = Asm()
                                    .AddData(strTrue, Alloc.String("true"))
                                    .AddData(strFalse, Alloc.String("false"))
                                    ++ (beforeSysCall [Reg.a0] [])
                                    .AddText([
                                        (RV.BEQZ(argReg, printFalse), "")
                                        (RV.LA(Reg.a0, strTrue), "String to print via syscall")
                                        (RV.J(printExec), "")
                                        (RV.LABEL(printFalse), "")
                                        (RV.LA(Reg.a0, strFalse), "String to print via syscall")
                                        (RV.LABEL(printExec), "")
                                        (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                                        (RV.ECALL, "")
                                    ])
                                    ++ (afterSysCall [Reg.a0] [])
            { argLoadRes with Asm = argLoadRes.Asm ++ boolPrintCode }
        | TInt ->
            /// Printout code for integer variables
            let intPrintCode = (beforeSysCall [Reg.a0] [])
                                    .AddText([
                                        (RV.MV(Reg.a0, argReg), "Copy to a0 for printing")
                                        (RV.LI(Reg.a7, 1), "RARS syscall: PrintInt")
                                        (RV.ECALL, "")
                                    ])
                               ++ (afterSysCall [Reg.a0] [])
            { argLoadRes with Asm = argLoadRes.Asm ++ intPrintCode }
        | TString ->
            /// Printout code for string variables
            let stringPrintCode = (beforeSysCall [Reg.a0] [])
                                      .AddText([
                                          (RV.MV(Reg.a0, argReg), "Copy to a0 for printing")
                                          (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                                          (RV.ECALL, "")
                                      ])
                                  ++ (afterSysCall [Reg.a0] [])
            { argLoadRes with Asm = argLoadRes.Asm ++ stringPrintCode }
        | TStruct fields ->
            let nodes = 
                [{ init with Expr = StringVal("struct { "); Type = TString }] @
                (List.collect (fun (name, tpe, _) ->
                    let strVals = 
                        match tpe with
                        | TString -> (name + @" = \"""), @"\""; "
                        | _ -> (name + " = "), "; "
                    [
                        { init with Expr = StringVal(fst strVals); Type = TString }
                        { init with Expr = FieldSelect(arg, name); Type = TString }
                        { init with Expr = StringVal(snd strVals); Type = TString }
                    ]
                ) fields) @
                [{ init with Expr = StringVal("}"); Type = TString }]
            let printoutBinders = prebindPrintTarget nodes
            // let temp = doLetInitCodegen env { init with Expr = Seq(printoutBinders) }
            // Skip detailed printout of complex data types in codegen/interpreter
            // #TODO: move printout AST in an earlier compilation phase - `parser`
            argLoadRes
        | TArray tpe ->
            let nodes = [
                { init with Expr = Print(
                        { init with Expr = StringVal(
                                $"Array{{ type: {tpe.ToString()}; length: "); Type = TString }) }
                { init with Expr = Print({ init with Expr = ArrayLength(arg); Type = TInt }) }
                { init with Expr = Print({ init with Expr = StringVal(" }"); Type = TString }) }
            ]
            let printoutBinders = prebindPrintTarget nodes
            // let temp = doLetInitCodegen env { init with Expr = Seq(printoutBinders) }
            // Skip detailed printout of complex data types in codegen/interpreter
            // #TODO: move printout AST in an earlier compilation phase - `parser`
            argLoadRes
        | TFun _ as t ->
            doLetInitCodegen env
                { init with Expr = Let(env.TargetVar,
                        { init with Expr = StringVal(t.ToString()); Type = TString },
                        { init with Expr = Print({ init with Expr = Var(env.TargetVar) }) })
                }

        | TUnion _ as t ->
            doLetInitCodegen env
                { init with Expr = Let(env.TargetVar,
                        { init with Expr = StringVal(t.ToString()); Type = TString },
                        { init with Expr = Print({ init with Expr = Var(env.TargetVar) }) })
                }
                
        | t -> failwith $"BUG: Print int-like codegen invoked on unsupported type %O{t}"
        

    | PrintLn(arg) ->
        /// Recycle codegen for Print above, then also output a newline token
        let printRes = doLetInitCodegen env { init with Expr = Print(arg) }
        
        /// Add the newline character
        let newlineAsm =
            (beforeSysCall [Reg.a0] []) ++        
            Asm([
                (RV.LI(Reg.a0, int('\n')), "Character to print (newline)")
                (RV.LI(Reg.a7, 11), "RARS syscall: PrintChar")
                (RV.ECALL, "")
            ])
            ++ (afterSysCall [Reg.a0] [])
        { Asm = printRes.Asm ++ newlineAsm
          Env = printRes.Env }

    | Assertion(arg) ->
        /// Register holding assertion argument, and code to load it
        let argReg, argLoadRes = loadIntVar env (getVarName arg) []
        /// Label to jump to when the assertion is true
        let passLabel = Util.genSymbol "assert_true"
        /// Target register to store the assertion bool value + code to load it
        let targetReg, targetLoadRes =
                loadIntVar argLoadRes.Env env.TargetVar [getVarName arg]
        /// Assembly code for the assertion: check the assertion, and jump
        /// to 'passLabel' if it is true; otherwise, fail
        let assertAsm = Asm([
            (RV.ADDI(targetReg, argReg, Imm12(-1)), "")
            (RV.BEQZ(targetReg, passLabel), "Jump if assertion OK")
            (RV.LI(Reg.a7, 93), "RARS syscall: Exit2")
            (RV.LI(Reg.a0, RISCVCodegen.assertExitCode), "Assertion violation exit code")
            (RV.ECALL, "")
            (RV.LABEL(passLabel), "") ])
        { Asm = argLoadRes.Asm ++ targetLoadRes.Asm ++ assertAsm;
          Env = targetLoadRes.Env }

    | If(condition, ifTrue, ifFalse) ->
        /// Register holding 'if' condition, and code to load it
        let condReg, condLoadRes = loadIntVar env (getVarName condition) []
        /// Code generation result for the 'true' branch
        let trueCodegenRes = doCodegen condLoadRes.Env ifTrue
        /// Code generation result for the 'false' branch
        let falseCodegenRes = doCodegen condLoadRes.Env ifFalse
        /// Assembly code to spill/load variables after the 'false' branch, to
        /// get the same register allocation obtained after the 'true' branch
        let syncAsm = syncANFCodegenEnvs falseCodegenRes.Env trueCodegenRes.Env

        /// Label to jump to when the 'if' condition is true
        let labelTrue = Util.genSymbol "if_true"
        /// Label to jump to when the 'if' condition is false
        let labelFalse = Util.genSymbol "if_false"
        /// Label to mark the end of the `if...then...else` code
        let labelEnd = Util.genSymbol "if_end"

        /// Assembly code for the whole 'if' expression. NOTE: this code generation is simplified,
        /// and it fails if the address of 'labelFalse' or 'labelEnd' is more than 2048 bytes far
        /// from the corresponding J instructions. A better approach would be to load the label
        /// into a register (using the instruction LA) and then jump using  the instruction JR:
        /// this would be similar to the 'if' compilation in RISCVCodegen.fs ---  but this approach
        /// would consume one additional register, and possibly require the spilling of a variable
        let ifAsm =
            condLoadRes.Asm
                .AddText([ (RV.BNEZ(condReg, labelTrue),
                            "Jump when 'if' condition is true")
                           (RV.J(labelFalse),
                            "Jump to the 'false' branch of the 'if' code")
                           (RV.LABEL(labelTrue),
                            "Beginning of the 'true' branch of the 'if' code") ])
            ++ trueCodegenRes.Asm
                .AddText([ (RV.J(labelEnd),
                            "Jump to skip the 'false' branch of 'if' code")
                           (RV.LABEL(labelFalse),
                            "Beginning of the 'false' branch of the 'if' code") ])
            ++ falseCodegenRes.Asm
            ++ Asm(RV.COMMENT("Branch synchronization code begins here"))
            ++ syncAsm
            ++ Asm(RV.COMMENT("Branch synchronization code ends here"))
                .AddText(RV.LABEL(labelEnd), "End of the 'if' code")
        { Asm = ifAsm
          Env = trueCodegenRes.Env }
    
    | While(condition, body) ->
        // #TODO: See mut_array_bug for environment synchronization issues around while-loops
        
        /// Updated ANF codegen environment for the condition piece of the loop (add needed vars + set cond. target)
        let conditionEnv = { env with
                                NeededVars = Set.union env.NeededVars (ASTUtil.freeVars body) }
        
        /// Code generation result for the loop condition assumed in ANF
        let condCodegenRes = doCodegen conditionEnv condition
        let condReg = getIntVarRegister condCodegenRes.Env env.TargetVar
        
        /// Code generation result for the 'while' loop body assumed in ANF
        let bodyCodegenRes = doCodegen { condCodegenRes.Env with TargetVar = env.TargetVar } body
        /// Assembly code to spill/load variables after the 'while' body, to get the same
        /// register allocation obtained before entering the 'while' condition.
        /// Sync the full loop environment back to the condition entry state
        let syncAsm = syncANFCodegenEnvs bodyCodegenRes.Env condCodegenRes.Env
        
        /// Label to mark the beginning of the 'while' loop
        let whileBeginLabel = Util.genSymbol "while_loop_begin"
        /// Label to mark the beginning of the 'while' loop body
        let whileBodyBeginLabel = Util.genSymbol "while_body_begin"
        /// Label to mark the end of the 'while' loop
        let whileEndLabel = Util.genSymbol "while_loop_end"
        
        // Check the 'while' condition, jump to 'whileEndLabel' if it is false.
        // Here we use a register to load the address of a label (using the
        // instruction LA) and then jump to it (using the instruction LR): this
        // way, the label address can be very far from the jump instruction
        // address --- and this can be important if the compilation of 'body'
        // produces a large amount of assembly code
        let whileAsm =
            Asm(RV.LABEL(whileBeginLabel))
            ++ condCodegenRes.Asm
                   .AddText([
                        (RV.BNEZ(condReg, whileBodyBeginLabel),
                         "Jump to the loop body if the 'while' condition is true")
                        (RV.J(whileEndLabel),
                         "Jump to the end of the 'while' loop")
                        (RV.LABEL(whileBodyBeginLabel),
                         "Body of the 'while' loop begins here")
                   ])
            ++ bodyCodegenRes.Asm
            ++ Asm(RV.COMMENT("Branch synchronization code begins here"))
            ++ syncAsm
            ++ Asm(RV.COMMENT("Branch synchronization code ends here"))
            ++ Asm([
                    (RV.J(whileBeginLabel),
                     "Jump to the the start of the loop construct")
                    (RV.LABEL(whileEndLabel), "")
                ])
        { Asm = whileAsm
          Env = { condCodegenRes.Env with NeededVars = env.NeededVars } }
        
    | DoWhile(body, condition) ->
        /// Code generation result for the 'do-while' loop body
        let bodyCodegenRes = doCodegen env body
        /// Register holding 'do-while' condition as variable, and code to load it
        let condReg, condLoadRes = loadIntVar bodyCodegenRes.Env (getVarName condition) []
        /// Assembly code to spill/load variables after the 'do-while' body, to get the same
        /// register allocation obtained after the 'do-while' condition and body code generation
        let syncAsm = syncANFCodegenEnvs condLoadRes.Env env
    
        /// Label to mark the beginning of the 'do-while' loop body
        let doWhileBodyBeginLabel = Util.genSymbol "do_while_body_begin"
        
        let doWhileAsm =
            Asm(RV.LABEL(doWhileBodyBeginLabel))
            ++ bodyCodegenRes.Asm
            ++ condLoadRes.Asm
            ++ Asm(RV.COMMENT("Branch synchronization code begins here"))
            ++ syncAsm
            ++ Asm(RV.COMMENT("Branch synchronization code ends here"))
            ++ Asm(RV.BNEZ(condReg, doWhileBodyBeginLabel),
                     "Jump to the start of the loop body if the 'do-while' condition is true")
        { Asm = doWhileAsm
          Env = condLoadRes.Env }

    | Seq nodes ->
        /// Collect the code of each sequence node assumed in ANF by folding over all children
        let folder (acc: ANFCodegenResult) (node: TypedAST) =
            let result = doCodegen acc.Env node
            { Asm = acc.Asm ++ result.Asm
              Env = result.Env }
        List.fold folder { Asm = Asm(); Env = env } nodes

    | Type(_, _, scope) ->
        // Type aliases don't produce any code --- but their ANF scope does
        doCodegen env scope

    | Ascription(_, node) ->
        // Ascriptions don't produce any code --- but their type-annotated
        // expression must be a variable, producing code for it
        doCodegen env node
        
    | Assign(lhs, rhs) ->
        /// Extracted variable name from rhs
        let rhsVarName = getVarName rhs
        
        match lhs.Expr with
        | Var(name) ->
            match rhs.Type with
            | t when (isSubtypeOf rhs.Env t TUnit) ->
                // Nothing to perform for unit assignments
                { Asm = Asm()
                  Env = env }
            | t when (isSubtypeOf rhs.Env t TFloat) ->
                /// Register holding the assigning variable (rhs.) and ANF codegen result to load it
                let rhsReg, rhsLoadCode = loadFloatVar env rhsVarName []
                
                /// Register holding the target variable with the result of the assignment, and ANF code to load it
                /// The assignee variable is protected from spilling when loading the target register.
                let targetFpReg, loadTargetReg = loadFloatVar rhsLoadCode.Env env.TargetVar [rhsVarName]
                
                match findFloatVarRegister env name with
                | Some(fpReg) ->
                    let assignCode = rhsLoadCode.Asm
                                     ++ Asm(RV.FMV_S(fpReg, rhsReg),
                                        $"Assignment to variable %s{name}")
                                     ++ loadTargetReg.Asm
                                     ++ Asm(RV.FMV_S(targetFpReg, rhsReg),
                                        $"Output of assignment to target")
                    { Asm = assignCode
                      Env = loadTargetReg.Env }
                | None ->
                    let offset = rhsLoadCode.Env.Frame.Item name
                    let assignCode = rhsLoadCode.Asm
                                     ++ Asm(RV.FSW_S(rhsReg, Imm12(offset * -4), Reg.fp),
                                        $"Assignment to variable %s{name} on stack at offset %d{offset}")
                                     ++ loadTargetReg.Asm
                                     ++ Asm(RV.FMV_S(targetFpReg, rhsReg),
                                        $"Output of assignment to target")
                    { Asm = assignCode
                      Env = loadTargetReg.Env }
            | _ ->
                /// Register holding the assigning variable (rhs.) and ANF codegen result to load it
                let rhsReg, rhsLoadCode = loadIntVar env rhsVarName []
                
                /// Register holding the target variable with the result of the assignment, and ANF code to load it
                /// The assignee variable is protected from spilling when loading the target register.
                let targetReg, loadTargetReg = loadIntVar rhsLoadCode.Env env.TargetVar [rhsVarName]
                
                match findIntVarRegister env name with
                | Some(reg) ->
                    let assignCode = rhsLoadCode.Asm
                                     ++ Asm(RV.MV(reg, rhsReg),
                                        $"Assignment to variable %s{name}")
                                     ++ loadTargetReg.Asm
                                     ++ Asm(RV.MV(targetReg, rhsReg),
                                        $"Output of assignment value to target")
                    { Asm = assignCode
                      Env = loadTargetReg.Env }
                | None ->
                    let offset = rhsLoadCode.Env.Frame.Item name
                    let assignCode = rhsLoadCode.Asm
                                     ++ Asm(RV.SW(rhsReg, Imm12(offset * -4), Reg.fp),
                                        $"Assignment to variable %s{name} on stack at offset %d{offset}")
                                     ++ loadTargetReg.Asm
                                     ++ Asm(RV.MV(targetReg, rhsReg),
                                        $"Output of assignment value to target")
                    { Asm = assignCode
                      Env = loadTargetReg.Env }

        | FieldSelect(structure, field) ->
            /// Extracted variable name for the structure object
            let structVarName = getVarName structure

            /// Register holding the structure object (heap memory address)
            let structReg, structLoadRes = loadIntVar env structVarName []
            
            match expandType structure.Env structure.Type with
            | TStruct(fields) ->
                /// Names of the struct fields
                let fieldNames, _, _ = List.unzip3 fields
                
                /// Offset of the selected struct field from the beginning of the struct
                let offset = List.findIndex (fun f -> f = field) fieldNames
                
                /// Assembly code that performs the field value assignment
                let assignResult =
                    match rhs.Type with
                    | t when (isSubtypeOf rhs.Env t TUnit) ->
                        // Nothing to do
                        { Asm = Asm()
                          Env = env }
                    | t when (isSubtypeOf rhs.Env t TFloat) ->
                        /// Register holding the assignee variable (rhs.) and ANF codegen result to load it
                        let rhsFpReg, rhsLoadRes = loadFloatVar structLoadRes.Env rhsVarName [structVarName]
                        
                        /// Register holding the target variable with the result of the assignment, and ANF code to load it
                        /// The assignee variable is protected from spilling when loading the target register.
                        let targetFpReg, loadTargetRes = loadFloatVar rhsLoadRes.Env env.TargetVar [rhsVarName]
                        
                        let assignCode =
                            structLoadRes.Asm
                            ++ rhsLoadRes.Asm
                            ++ Asm(RV.FSW_S(rhsFpReg, Imm12(offset * 4), structReg),
                               $"Assigning value to struct field '%s{field}'")
                            ++ loadTargetRes.Asm
                            ++ Asm(RV.FMV_S(targetFpReg, rhsFpReg),
                               $"Output of assignment value to target")
                        
                        { Asm = assignCode
                          Env = loadTargetRes.Env }
                        
                    | _ ->
                        /// Register holding the assignee variable (rhs.) and ANF codegen result to load it
                        let rhsReg, rhsLoadRes = loadIntVar structLoadRes.Env rhsVarName [structVarName]
                        
                        /// Register holding the target variable with the result of the assignment, and ANF code to load it
                        /// The assignee variable is protected from spilling when loading the target register.
                        let targetReg, loadTargetRes = loadIntVar rhsLoadRes.Env env.TargetVar [rhsVarName]
                        
                        let assignCode =
                            structLoadRes.Asm
                            ++ rhsLoadRes.Asm
                            ++ Asm(RV.SW(rhsReg, Imm12(offset * 4), structReg),
                               $"Assigning value to struct field '%s{field}'")
                            ++ loadTargetRes.Asm
                            ++ Asm(RV.MV(targetReg, rhsReg),
                               $"Output of assignment value to target")
                        { Asm = assignCode
                          Env = loadTargetRes.Env }
                assignResult
            | t ->
                failwith $"BUG: field selection on invalid object type: %O{t}"
        
        | ArrayElem(arrTarget, index) ->
            /// Extract the targeted array & index variable name
            let arrayVarName = getVarName arrTarget
            let indexVarName = getVarName index
            
            /// Register holding the array variable (memory address of structure) and ANF code to load it
            let arrayReg, arrayLoadRes = loadIntVar env arrayVarName []
            
            /// Register holding the selected index for writing the array element and ANF code to load it
            let indexReg, indexLoadRes = loadIntVar arrayLoadRes.Env indexVarName [arrayVarName]
            
            let boundErrorLabel = Util.genSymbol "index_out_of_bound_error"
            let checkPassLabel = Util.genSymbol "bound_check_pass"
        
            /// Assembly code for verifying index bounds
            let boundsCheckCode = Asm([
                (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space")
                (RV.SW(arrayReg, Imm12(0), Reg.sp), "Save array pointer on stack")
                (RV.LW(arrayReg, Imm12(0), arrayReg), "Load length from array struct (1st field)")
                (RV.BGE(indexReg, arrayReg, boundErrorLabel), "Check index >= length")
                (RV.BLTZ(indexReg, boundErrorLabel), "Check index < 0")
                (RV.J(checkPassLabel), "Continue if bound checks are satisfied")
                (RV.LABEL(boundErrorLabel), "")
                (RV.LI(Reg.a7, 93), "RARS syscall: Exit2")
                (RV.LI(Reg.a0, RISCVCodegen.assertExitCode), "Assertion violation exit code")
                (RV.ECALL, "")
                (RV.LABEL(checkPassLabel), "")
                (RV.LW(arrayReg, Imm12(0), Reg.sp), "Restore array pointer from stack")
                (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")
            ])
            
            /// ANF codegen result for modifying the selected array element
            let elementModifyRes =
                match expandType arrTarget.Env arrTarget.Type with
                | TArray t when isSubtypeOf arrTarget.Env t TUnit ->
                    { Asm = Asm(); Env = env } // Nothing to do
                | TArray t when isSubtypeOf arrTarget.Env t TInt ->
                    /// Offset of the selected index from the beginning of the array data container on heap
                    let offsetCode = Asm([
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space")
                        (RV.SW(arrayReg, Imm12(0), Reg.sp), "Save array struct pointer on stack")
                        (RV.LW(arrayReg, Imm12(4), arrayReg),
                         "Load data container pointer from array struct (2nd field)")
                        
                        // Array element address
                        (RV.SLLI(indexReg, indexReg, Shamt(2u)),
                         "Calculate offset of selected element = index * 4")
                        (RV.ADD(arrayReg, arrayReg, indexReg),
                         "Element address = container base address + word-aligned offset")
                        
                        (RV.SRLI(indexReg, indexReg, Shamt(2u)),
                         "Restore index value by dividing it by word size")
                    ])
                    
                    /// Register holding the assigning variable (rhs.) and ANF codegen result to load it
                    let rhsReg, rhsLoadRes = loadIntVar indexLoadRes.Env rhsVarName [arrayVarName]
                    
                    /// Register holding the target assigned value and ANF code to load it
                    let targetReg, targetLoadRes = loadIntVar rhsLoadRes.Env env.TargetVar [arrayVarName]
                    
                    /// Assembly code that performs the array element assignment
                    let assignmentCode = Asm([
                        (RV.SW(rhsReg, Imm12(0), arrayReg),
                         "Store assigned value into selected array element")
                        (RV.LW(arrayReg, Imm12(0), Reg.sp), "Restore array struct pointer from stack")
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")
                        (RV.MV(targetReg, rhsReg),
                         "Output of assignment value to target")
                    ])
                    
                    { Asm = offsetCode
                            ++ targetLoadRes.Asm
                            ++ rhsLoadRes.Asm
                            ++ assignmentCode
                      Env = targetLoadRes.Env }
                    
                | TArray t when isSubtypeOf arrTarget.Env t TFloat ->
                    /// Offset of the selected index from the beginning of the array data container on heap
                    let offsetCode = Asm([
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space")
                        (RV.SW(arrayReg, Imm12(0), Reg.sp), "Save array struct pointer on stack")
                        (RV.LW(arrayReg, Imm12(4), arrayReg),
                         "Load data container pointer from array struct (2nd field)")
                        
                        // Word-aligned index offset
                        (RV.SLLI(indexReg, indexReg, Shamt(2u)),
                         "Calculate offset of selected element = index * 4")
                        
                        // Address of selected element
                        (RV.ADD(arrayReg, arrayReg, indexReg),
                         "Element address = container base address + word-aligned offset")
                    ])
                    
                    /// Register holding the target assigned value and ANF code to load it
                    let targetFpReg, targetLoadRes =
                        loadFloatVar indexLoadRes.Env env.TargetVar [arrayVarName; indexVarName]                    
                    
                    /// Register holding the assigning variable (rhs.) and ANF codegen result to load it
                    let rhsFpReg, rhsLoadRes = loadFloatVar targetLoadRes.Env rhsVarName [arrayVarName; env.TargetVar]
                    
                    /// Assembly code that performs the array element assignment
                    let assignmentCode = Asm([
                        (RV.FSW_S(rhsFpReg, Imm12(0), arrayReg),
                         "Store assigned value into selected array element")
                        (RV.FMV_S(targetFpReg, rhsFpReg),
                         "Output of assignment value to target")
                        
                        // Restore index and array struct pointer values
                        (RV.SRLI(indexReg, indexReg, Shamt(2u)),
                         "Restore index value by dividing it by word size")
                        (RV.LW(arrayReg, Imm12(0), Reg.sp), "Restore array struct pointer from stack")
                        (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")
                    ])
                    
                    { Asm = targetLoadRes.Asm
                            ++ offsetCode
                            ++ rhsLoadRes.Asm
                            ++ assignmentCode
                      Env = rhsLoadRes.Env }
                    
                | _ -> failwith $"BUG: array element writing on invalid array type: %O{arrTarget.Type}"
            
            { Asm = arrayLoadRes.Asm
                    ++ indexLoadRes.Asm
                    ++ boundsCheckCode
                    ++ elementModifyRes.Asm
              Env = elementModifyRes.Env }
        | _ -> failwith $"ANF Assignment not yet implemented for {lhs.Expr}"

           
    | StructCons fields ->
        /// Allocate a new struct variable on heap, and get the code to do it
        let structStorageReg, structStorageCode = loadIntVar env env.TargetVar []
        let fieldNames, fieldInitNodes = List.unzip fields
        /// List of variable names associated with the expression in initializers
        let anfInitLabels = getVarNames fieldInitNodes 
        
        /// Generate code to initialize a struct field and accumulate the result.
        /// Function is folded over all indexed struct fields, to initialize all of them.
        let fieldLoader = fun (acc: ANFCodegenResult) (fieldOffset: int, label: string) ->
            // Code to initialize a single struct field. Each field is compiled by targeting
            // the specific variable name of the initialization expression, while preserving the
            // target variable in registers as the whole struct address.The variable content is
            // loaded on the heap location with word-aligned offset from the base address.
            
            /// Record the specific init node at the given offset
            let fieldInit = fieldInitNodes[fieldOffset]
            
            match fieldInit.Type with
            | t when isSubtypeOf fieldInit.Env t TFloat ->
                /// Register holding the field initializer variable, and code to load it
                let (initFpReg, initLoadRes) = loadFloatVar acc.Env label [env.TargetVar]
                
                /// Code to set the field at offset heap location with initializer
                let fieldInitCode =
                    Asm(RV.FSW_S(initFpReg, Imm12(fieldOffset * 4), structStorageReg),
                        $"Initialize struct field '{fieldNames[fieldOffset]}' with init label - '{label}'")
                
                { Asm = acc.Asm ++ initLoadRes.Asm ++ fieldInitCode
                  Env = initLoadRes.Env }
            | _ ->
                /// Register holding the field initializer variable, and code to load it
                let (initReg, initLoadRes) = loadIntVar acc.Env label [env.TargetVar]
                
                /// Code to set the field at offset heap location with initializerYo
                let fieldInitCode =
                    Asm(RV.SW(initReg, Imm12(fieldOffset * 4), structStorageReg),
                        $"Initialize struct field '{fieldNames[fieldOffset]}' with init label - '{label}'")
                
                // Update the accumulator with the code and environment
                { Asm = acc.Asm ++ initLoadRes.Asm ++ fieldInitCode
                  Env = initLoadRes.Env }
        
        /// Code to allocate the whole struct on the heap
        let fieldsInitRes = List.fold fieldLoader
                                { Asm = Asm(); Env = structStorageCode.Env }
                                (List.indexed anfInitLabels)
        
        /// Assembly code that allocates space on the heap for the new structure.
        /// Performs a 'Sbrk' system call, with the size of structure: word-aligned
        /// number of fields - 4 x no. fields
        let structAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.LI(Reg.a0, fields.Length * 4),
                     "Amount of memory to allocate for a struct (bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk") // Register restore by default
                    (RV.ECALL, "")
                    (RV.MV(structStorageReg, Reg.a0),
                     "Move syscall result (struct mem address) to target variable")
                ])
                ++ (afterSysCall [Reg.a0] [])
        
        { Asm = structStorageCode.Asm ++ structAllocCode ++ fieldsInitRes.Asm
          Env = fieldsInitRes.Env }
        
    | FieldSelect(target, field) ->
        /// Extract variable name for selected structure
        let structVarName = getVarName target
        
        /// Register holding the structure variable (memory address of object) and ANF code to load it
        let structReg, structLoadRes = loadIntVar env structVarName []

        /// Codegen result for performing the field access once the target struct is loaded.
        let fieldAccessRes =
            match expandType init.Env target.Type with
            | TStruct(fields) ->
                let fieldNames, fieldTypes, _ = List.unzip3 fields
                /// Compute the offset with respect to the list of fields in the struct
                let offset = List.findIndex (fun f -> f = field) fieldNames
                
                // Based on the type of the selected field perform the computation into the target variable
                match expandType init.Env fieldTypes[offset] with
                | TUnit -> { Asm = Asm(); Env = structLoadRes.Env } // Nothing to do
                | TFloat ->
                    /// Target register to store the field selection result, and code to load it
                    let selectFpReg, selectRes = loadFloatVar structLoadRes.Env env.TargetVar []
                    let selectionCode =
                            Asm(RV.FLW_S(selectFpReg, Imm12(offset * 4), structReg),
                            $"Retrieve value of struct field '%s{field}'")
                    { Asm = selectRes.Asm ++ selectionCode
                      Env = selectRes.Env }
                | _ ->
                    /// Target register to store the field selection result, and code to load it
                    let selectReg, selectRes = loadIntVar structLoadRes.Env env.TargetVar []
                    let selectionCode =
                            Asm(RV.LW(selectReg, Imm12(offset * 4), structReg),
                            $"Retrieve value of struct field '%s{field}'")
                    { Asm = selectRes.Asm ++ selectionCode
                      Env = selectRes.Env }
            | t -> failwith $"BUG: FieldSelect codegen on invalid target type: %O{t}"
        { Asm = structLoadRes.Asm ++ fieldAccessRes.Asm
          Env = fieldAccessRes.Env}
    
    | Lambda(args, body) ->
        /// Label to mark the position of the lambda term body
        let funLabel = Util.genSymbol "lambda"
        
        /// Names of the lambda arguments
        let argNames, _ = List.unzip args
        
        /// Types of the lambda arguments - retrieved from type-checker environment
        let argTypes = List.map (fun a -> body.Env.Vars[a]) argNames
        
        /// Perform the ANF closure conversion on the lambda term, for immutable variable closures
        // closureConversion env funLabel init None args argTypes body
        failwith "Missing closure conversion implementation"
        
    | Application(func, args) ->
        /// Integer caller-saved registers to be stored on stack before executing
        /// the function call, and restored when the function returns.
        let saveRegs = (Reg.ra :: [for i in 0u..7u do yield Reg.a(i)]
                                @ [for i in 0u..6u do yield Reg.t(i)])
        /// List of FP registers to save as a caller convention - we save `fa` and `ft` here
        let saveFpRegs = ([for i in 0u..7u do yield FPReg.fa(i)]
                        @ [for i in 0u..11u do yield FPReg.ft(i)])
        
        /// Extract variable name for function
        let funVarName = getVarName func
        
        /// Register holding the function variable and ANF code to load it
        let functionReg, functionLoadRes = loadIntVar env funVarName []
                
        let closurePlainFunAccessCode = Asm(RV.LW(functionReg, Imm12(0), functionReg),
                                            "Load plain function address `@f` from closure")
        
        /// Assembly code for the expression being applied as a function
        let appTermCode =
            Asm().AddText(RV.COMMENT("Load expression to be applied as function"))
            ++ functionLoadRes.Asm
            ++ closurePlainFunAccessCode
        
        /// Indexed list of argument expressions split by type.  We will use the index
        /// as an offset (above the current target register) to determine the target
        /// register for compiling each expression.
        let indexedArgsFloat, indexedArgsInt =
            [func] @ args
            |> List.partition (fun arg -> isSubtypeOf arg.Env arg.Type TFloat)
            |> fun (floats, ints) -> (List.indexed floats, List.indexed ints)
        
        /// Function that copies the content of an argument variable from temp registers to
        /// `a#` registers using the argument index to determine the destination (opt. on stack).
        /// The assembly code is accumulated over all arguments of the function.
        let compileCopyArg (acc: ANFCodegenResult) (i: int, arg:TypedAST) (wordOffset: int) =
            let argVarName = getVarName arg
            let argOffset = (i - 8 + wordOffset) * 4
            
            
            match arg.Type with
            | t when (isSubtypeOf arg.Env t TFloat) ->
                /// Register holding the float argument variable and ANF codegen result to load it
                let argFpReg, argLoadRes = loadFloatVar acc.Env argVarName []
                
                if i < 8 then
                    let loadCopyCode = Asm(RV.FMV_S(FPReg.fa(uint i), argFpReg),
                                       $"Load float function call argument %d{i+1} to target FP register `fa%d{i}`")
                    { Asm = acc.Asm ++ argLoadRes.Asm ++ loadCopyCode
                      Env = argLoadRes.Env }
                else
                    let stackStoreCode = Asm(RV.FSW_S(argFpReg, Imm12(argOffset), Reg.sp),
                                         $"Store float function call argument %d{i+1} to stack at offset {argOffset}")
                    { Asm = acc.Asm ++ argLoadRes.Asm ++ stackStoreCode
                      Env = argLoadRes.Env }
            | _ ->
                /// Register holding the float argument variable and ANF codegen result to load it
                let argReg, argLoadRes = loadIntVar acc.Env argVarName []
                
                if i < 8 then
                    let loadCopyCode = Asm(RV.MV(Reg.a(uint i), argReg),
                                       $"Load function call argument %d{i+1} to register `a%d{i}`")
                    { Asm = acc.Asm ++ argLoadRes.Asm ++ loadCopyCode
                      Env = argLoadRes.Env }
                else
                    let stackStoreCode = Asm(RV.SW(argReg, Imm12(argOffset), Reg.sp),
                                         $"Store function call argument %d{i+1} to stack at offset {argOffset}")
                    { Asm = acc.Asm ++ argLoadRes.Asm ++ stackStoreCode
                      Env = argLoadRes.Env }
        
        let floatArgsOnStack = max 0 (indexedArgsFloat.Length - 8)
        let intArgsOnStack = max 0 (indexedArgsInt.Length - 8)
        
        /// Code that loads each application argument variable into a register `a`, by copying
        /// the contents of argument variables. The code folds over the indices of all arguments
        /// (from 0 to args.Length), using `compileCopyArg` above.
        let argsLoadCode =
            /// Calculate the exact number of arguments that overflow to stack (for allocation)
            let stackAdjustment =
                let argsOnStack = floatArgsOnStack + intArgsOnStack
                if argsOnStack > 0 then
                    { Asm = Asm(RV.ADDI(Reg.sp, Reg.sp, Imm12(-4 * argsOnStack)),
                            $"Update stack pointer for the overflowing args with overflow of %d{argsOnStack} units")
                      Env = functionLoadRes.Env } 
                else
                    { Asm = Asm()
                      Env = functionLoadRes.Env }
            
            let floatArgsLoadCode = List.fold
                                        (fun acc arg -> compileCopyArg acc arg 0)
                                        stackAdjustment
                                        indexedArgsFloat
            let floatIntArgsLoadCode =
                List.fold
                        (fun acc arg -> compileCopyArg acc arg floatArgsOnStack)
                        floatArgsLoadCode
                        indexedArgsInt

            floatIntArgsLoadCode
            
        /// Assembly code that performs the function call
        let callCode =
            appTermCode
                .AddText(RV.COMMENT("Before function call: save caller-saved registers"))
               ++ (saveRegisters saveRegs saveFpRegs)
               ++ argsLoadCode.Asm // Code to load arg values into arg registers
                  .AddText(RV.JALR(Reg.ra, Imm12(0), functionReg), "Function call")
        
        /// Code handling the function return value (if any)
        /// If a function expression, we check its return type to target the correct
        /// output register, FPReg for float and Reg for int.
        let returnCode =
            match func.Type with
            | TFun(_, retType) ->
                match retType with
                | TFloat ->
                    let returnFpReg, returnLoadRes =
                        loadFloatVar argsLoadCode.Env env.TargetVar [] 
                    { returnLoadRes with Asm = returnLoadRes.Asm ++
                                                Asm(RV.FMV_S(returnFpReg, FPReg.fa0),
                                                $"Copy function return value to return FP register") }
                | _ ->
                    let returnReg, returnLoadRes =
                        loadIntVar argsLoadCode.Env env.TargetVar []
                    { returnLoadRes with Asm = returnLoadRes.Asm ++
                                                Asm(RV.MV(returnReg, Reg.a0),
                                                $"Copy function return value to target register") }
            | _ -> failwith ""
        
        /// Combine everything together, and restore the caller-saved registers
        let applicationCode =
            callCode
                .AddText(RV.COMMENT("After function call"))
                ++ returnCode.Asm
                .AddText([
                       (RV.ADDI(Reg.sp, Reg.sp, Imm12(4 * (floatArgsOnStack + intArgsOnStack))),
                        $"Restore SP by {floatArgsOnStack + intArgsOnStack} function args after function call")
                       (RV.COMMENT("Restore caller-saved registers"),"")
                        ])
                  ++ (restoreRegisters saveRegs saveFpRegs)
        { Asm = applicationCode
          Env = returnCode.Env }
        
    | ArrayCons(length, arrInit) ->
        // To compile an array constructor, we allocate heap space for the whole array instance
        // (struct + container), and then compile its initialisation once and for all elements,
        // storing each result in the corresponding heap location. The struct heap address will
        // end up in the 'target' register - i.e. the register will contain a pointer to the
        // first element of the allocated structure.
        
        /// Extract the length variable name
        let lengthVarName = getVarName length
        
        /// Register holding the array length variable, and ANF code to load it
        let lengthReg, lengthLoadRes = loadIntVar env lengthVarName []
        
        /// Register holding the array base address (heap memory address), and ANF code to load it
        let arrayStructReg, arrayStructLoadRes = loadIntVar lengthLoadRes.Env env.TargetVar [lengthVarName]
        
        /// Assembly code that allocates space on the heap for the new array sequence, through `Sbrk`
        /// system call. The size of the structure is word-aligned for the no. of elements: 4 x length (bytes)
        let arrayAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.SLLI(Reg.a0, lengthReg, Shamt(2u)),
                     "Amount of memory to allocate for the array sequence (in bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                    (RV.ECALL, "")
                    (RV.MV(arrayStructReg, Reg.a0),
                     "Move syscall result (data container point) to target")
                ])
            ++ (afterSysCall [Reg.a0] [])
            ++ Asm([
                // Store data container pointer on stack temporarily
                (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)),
                 "Allocate stack space: sp[0]=array base address")
                (RV.SW(arrayStructReg, Imm12(0), Reg.sp),
                 "Save data container pointer on stack")
            ])
        
        /// Allocation of heap space for the new array struct through a 'Sbrk'
        /// system call. The size of the structure is 8 bytes (2 fields x 4 bytes)
        let structAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.ADDI(Reg.a0, Reg.zero, Imm12(8)),
                     "Amount of memory to allocate for array struct (2 fields, in bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                    (RV.ECALL, "")
                    (RV.MV(arrayStructReg, Reg.a0),
                     "Move syscall result (struct mem address) to target")
                ])
            ++ (afterSysCall [Reg.a0] [])
            ++ Asm([
                (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)),
                 "Allocate stack space: sp[4]=array data container; sp[0]=array struct")
                (RV.SW(arrayStructReg, Imm12(0), Reg.sp),
                 "Save array struct pointer on stack")
            ])
        
        /// Assembly code to store the length of the array and data pointer in the array struct fields
        let instanceFieldSetCode = Asm([
            (RV.SW(lengthReg, Imm12(0), arrayStructReg),
            "Store array length at the beginning of the array memory (1st struct field)")
            (RV.LW(Reg.a0, Imm12(4), Reg.sp),
             "Load data container pointer from stack sp[4]")
            (RV.SW(Reg.a0, Imm12(4), arrayStructReg),
            "Store array container pointer in data (2nd struct field)")
        ])
        
        /// Setup code for loading the initialization variable and element assignment code
        let elementSetupCode: ANFCodegenResult * Asm = 
            match expandType arrInit.Env arrInit.Type with
            | TUnit -> { Asm = Asm(); Env = arrayStructLoadRes.Env }, Asm() // Nothing to do for unit initializers
            | TFloat ->
                /// Register holding the initialization variable, and ANF code to load it
                let initFpReg, initLoadRes =
                    loadFloatVar arrayStructLoadRes.Env (getVarName arrInit) [lengthVarName; env.TargetVar]

                /// Assembly code that initializes float array elements by assigning the pre-computed
                /// initialisation variable in `initReg` to the heap location of the next array element in `lengthReg`.
                let elemInitCode =
                    Asm(RV.FSW_S(initFpReg, Imm12(0), arrayStructReg),
                    $"Initialize next array element")

                initLoadRes, elemInitCode
            | _ ->
                /// Register holding the initialization variable, and ANF code to load it
                let initReg, initLoadRes =
                    loadIntVar arrayStructLoadRes.Env (getVarName arrInit) [lengthVarName; env.TargetVar]
                
                /// Assembly code that initializes float array elements by assigning the pre-computed
                /// initialisation variable in `initReg` to the heap location of the next array element in `lengthReg`.
                let elemInitCode =
                    Asm(RV.SW(initReg, Imm12(0), arrayStructReg),
                    $"Initialize next array element")
                
                initLoadRes, elemInitCode

        /// Extract the results of element setup code: loading initialisation variable and element assignments
        let initLoadRes, elemInitCode = elementSetupCode
        
        /// Assembly code for initialising each element of the array container with pre-computed init,
        /// by looping through the array length and storing the value on heap. The element offset from data
        /// pointer computed in register `target+2` and the element value in register `target+3`.
        let initArrayLoopRes =
            /// Label for array loop start
            let loopStartLabel = Util.genSymbol "array_init_loop_start"
            /// Label for array loop end
            let loopEndLabel = Util.genSymbol "array_init_loop_end"

            { Asm = Asm([
                        (RV.LW(arrayStructReg, Imm12(4), Reg.sp), "Load data container pointer from stack sp[4]")
                        (RV.LABEL(loopStartLabel), "Start of array initialisation loop")
                        (RV.BEQZ(lengthReg, loopEndLabel), "Exit loop if remaining length is 0")
                    ])
                    ++ elemInitCode ++
                    Asm([
                        (RV.ADDI(arrayStructReg, arrayStructReg, Imm12(4)),
                         "Increment element address by word size")
                        (RV.ADDI(lengthReg, lengthReg, Imm12(-1)), "Decrement remaining length")
                        (RV.BNEZ(lengthReg, loopStartLabel), "Loop back if remaining length is not 0")
                        (RV.LABEL(loopEndLabel), "End of array initialisation loop")
                    ])
              Env = initLoadRes.Env }
            
        let targetSetupCode = Asm([
            (RV.LW(arrayStructReg, Imm12(0), Reg.sp), "Load array struct pointer from stack sp[0]")
            (RV.ADDI(Reg.sp, Reg.sp, Imm12(8)), "Deallocated used stack space during array constructor")
        ])

        // Glue all phases of the array construction together
        { Asm = lengthLoadRes.Asm
                  ++ arrayStructLoadRes.Asm
                  ++ initLoadRes.Asm
                  ++ arrayAllocCode
                  ++ structAllocCode
                  ++ instanceFieldSetCode
                  ++ initArrayLoopRes.Asm
                  ++ targetSetupCode
          Env = initArrayLoopRes.Env }

    | ArrayLength arrTarget ->
        /// Extract the targeted array variable name
        let arrayVarName = getVarName arrTarget
        
        /// Register holding the pointer to the array structure and ANF code to load it
        let arrayReg, arrayLoadRes = loadIntVar env arrayVarName []
        
        /// Register holding the target register
        let targetReg, targetLoadRes = loadIntVar arrayLoadRes.Env env.TargetVar [arrayVarName]
        
        /// Access the length field at offset 0 of the array structure object
        let lengthAccessCode = Asm(RV.LW(targetReg, Imm12(0), arrayReg),
                                "Load array length from base pointer in memory")
        
        { Asm = arrayLoadRes.Asm ++ targetLoadRes.Asm ++ lengthAccessCode
          Env = targetLoadRes.Env }

    | ArrayElem(arrTarget, index) ->       
        /// Extract the targeted array & index variable name
        let arrayVarName = getVarName arrTarget
        let indexVarName = getVarName index
        
        /// Register holding the pointer to the array structure and ANF code to load it
        let arrayReg, arrayLoadRes = loadIntVar env arrayVarName []
        
        /// Register holding the selected index for reading the array element and ANF code to load it
        let indexReg, indexLoadRes = loadIntVar arrayLoadRes.Env indexVarName [arrayVarName]
        
        let boundErrorLabel = Util.genSymbol "index_out_of_bound_error"
        let checkPassLabel = Util.genSymbol "bound_check_pass"
        
        /// Assembly code for verifying index bounds
        let boundsCheckCode = Asm([
            (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space")
            (RV.SW(arrayReg, Imm12(0), Reg.sp), "Save array pointer on stack")
            (RV.LW(arrayReg, Imm12(0), arrayReg), "Load length from array struct (1st field)")
            (RV.BGE(indexReg, arrayReg, boundErrorLabel), "Check index >= length")
            (RV.BLTZ(indexReg, boundErrorLabel), "Check index < 0")
            (RV.J(checkPassLabel), "Continue if bound checks are satisfied")
            (RV.LABEL(boundErrorLabel), "")
            (RV.LI(Reg.a7, 93), "RARS syscall: Exit2")
            (RV.LI(Reg.a0, RISCVCodegen.assertExitCode), "Assertion violation exit code")
            (RV.ECALL, "")
            (RV.LABEL(checkPassLabel), "")
            (RV.LW(arrayReg, Imm12(0), Reg.sp), "Restore array pointer from stack")
            (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")
        ])
        
        let elementLoadRes, elementAccessCode =
            match expandType arrTarget.Env arrTarget.Type with
            | TArray t when isSubtypeOf arrTarget.Env t TUnit ->
                { Asm = Asm(); Env = indexLoadRes.Env }, Asm() // Nothing to do for unit arrays
                
            | TArray t when isSubtypeOf arrTarget.Env t TInt ->
                /// Register (final container) holding the selected element and ANF code to load it
                let elemReg, elemLoadRes = loadIntVar indexLoadRes.Env env.TargetVar [arrayVarName; indexVarName]        
                
                /// Assembly code for array element access
                let elementAccessCode = Asm([
                    (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space")
                    (RV.SW(arrayReg, Imm12(0), Reg.sp), "Save array struct pointer on stack")
                    (RV.LW(arrayReg, Imm12(4), arrayReg),
                     "Load data container pointer from array struct (2nd field)")
                    (RV.SLLI(indexReg, indexReg, Shamt(2u)),
                     "Calculate offset of selected element = index * 4")
                    (RV.ADD(arrayReg, arrayReg, indexReg),
                     "Element address = container base pointer + word-aligned offset")
                    (RV.LW(elemReg, Imm12(0), arrayReg),
                     "Load selected element value into target")
                    (RV.LW(arrayReg, Imm12(0), Reg.sp), "Restore array struct pointer from stack")
                    (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")
                    (RV.SRLI(indexReg, indexReg, Shamt(2u)),
                     "Restore index value by dividing it by word size")
                ])
                elemLoadRes, elementAccessCode
            
            | TArray t when isSubtypeOf arrTarget.Env t TFloat ->
                /// Register (final container) holding the selected element and ANF code to load it
                let elemFpReg, elemLoadRes = loadFloatVar indexLoadRes.Env env.TargetVar [arrayVarName; indexVarName]
                
                /// Assembly code for array element access
                let elementAccessCode = Asm([
                    (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space")
                    (RV.SW(arrayReg, Imm12(0), Reg.sp), "Save array struct pointer on stack")
                    (RV.LW(arrayReg, Imm12(4), arrayReg),
                     "Load data container pointer from array struct (2nd field)")
                    
                    // Word-aligned index offset
                    (RV.SLLI(indexReg, indexReg, Shamt(2u)),
                     "Calculate offset of selected element = index * 4")
                    
                    // Address of selected element
                    (RV.ADD(arrayReg, arrayReg, indexReg),
                     "Element address = container base pointer + word-aligned offset")
                    
                    // Read selected array element
                    (RV.FLW_S(elemFpReg, Imm12(0), arrayReg),
                     "Load selected element value into target")
                    // Restore index and array struct pointer values
                    (RV.SRLI(indexReg, indexReg, Shamt(2u)),
                     "Restore index value by dividing it by word size")
                    (RV.LW(arrayReg, Imm12(0), Reg.sp), "Restore array struct pointer from stack")
                    (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space")
                ])
                
                elemLoadRes, elementAccessCode
                
            | _ -> failwith $"BUG: array element reading on invalid array type: %O{arrTarget.Type}"
        
        { Asm = arrayLoadRes.Asm
                ++ indexLoadRes.Asm
                ++ boundsCheckCode
                ++ elementLoadRes.Asm
                ++ elementAccessCode
          Env = elementLoadRes.Env }
    
    | ArraySlice _ 
    | UnionCons _
    | Match _
    | Copy _ -> failwith $"BUG: Feature codegen not implemented for %O{init.Expr}"
    
    | Pointer _
    | LetMut _
    | LetRec _
    | LetT _ 
    | Let _ -> // let-binders are not permitted as initializers of 'let' expressions
        failwith ($"BUG: unsupported AST node for 'let' init, maybe not in ANF:%s{Util.nl}"
                + $"%s{PrettyPrinter.prettyPrint init}")


/// Generate code to save the given registers on the stack, before a RARS system
/// call. Register a7 (which holds the system call number) is backed-up by
/// default, so it does not need to be specified when calling this function.
and internal beforeSysCall (regs: List<Reg>) (fpregs: List<FPReg>): Asm =
    Asm(RV.COMMENT("Before system call: save registers"))
        ++ (saveRegisters (Reg.a7 :: regs) fpregs)

/// Generate code to restore the given registers from the stack, after a RARS
/// system call. Register a7 (which holds the system call number) is restored
/// by default, so it does not need to be specified when calling this function.
and internal afterSysCall (regs: List<Reg>) (fpregs: List<FPReg>): Asm =
    Asm(RV.COMMENT("After system call: restore registers"))
        ++ (restoreRegisters (Reg.a7 :: regs) fpregs)
        
/// Generate code to save the given lists of registers by using increasing
/// offsets from the stack pointer register (sp).
and internal saveRegisters (rs: List<Reg>) (fprs: List<FPReg>): Asm =
    /// Generate code to save standard registers by folding over indexed 'rs'
    let regSave (asm: Asm) (i, r) = asm.AddText(RV.SW(r, Imm12(i * 4), Reg.sp))
    /// Code to save standard registers
    let rsSaveAsm = List.fold regSave (Asm()) (List.indexed rs)

    /// Generate code to save floating point registers by folding over indexed
    /// 'fprs', and accumulating code on top of 'rsSaveAsm' above. Notice that
    /// we use the length of 'rs' as offset for saving on the stack, since those
    /// stack locations are already used to save 'rs' above.
    let fpRegSave (asm: Asm) (i, r) =
        asm.AddText(RV.FSW_S(r, Imm12((i + rs.Length) * 4), Reg.sp))
    /// Code to save both standard and floating point registers
    let regSaveCode = List.fold fpRegSave rsSaveAsm (List.indexed fprs)

    // Put everything together: update the stack pointer and save the registers
    Asm(RV.ADDI(Reg.sp, Reg.sp, Imm12(-4 * (rs.Length + fprs.Length))),
        "Update stack pointer to make room for saved registers")
      ++ regSaveCode

/// Generate code to restore the given lists of registers, that are assumed to
/// be saved with increasing offsets from the stack pointer register (sp)
and internal restoreRegisters (rs: List<Reg>) (fprs: List<FPReg>): Asm =
    /// Generate code to restore standard registers by folding over indexed 'rs'
    let regLoad (asm: Asm) (i, r) = asm.AddText(RV.LW(r, Imm12(i * 4), Reg.sp))
    /// Code to restore standard registers
    let rsLoadAsm = List.fold regLoad (Asm()) (List.indexed rs)

    /// Generate code to restore floating point registers by folding over
    /// indexed 'fprs', and accumulating code on top of 'rsLoadAsm' above.
    /// Notice that we use the length of 'rs' as offset for saving on the stack,
    /// since those stack locations are already used to save 'rs' above.
    let fpRegLoad (asm: Asm) (i, r) =
        asm.AddText(RV.FLW_S(r, Imm12((i + rs.Length) * 4), Reg.sp))
    /// Code to restore both standard and floating point registers
    let regRestoreCode = List.fold fpRegLoad rsLoadAsm (List.indexed fprs)

    // Put everything together: restore the registers and then the stack pointer
    regRestoreCode
        .AddText(RV.ADDI(Reg.sp, Reg.sp, Imm12(4 * (rs.Length + fprs.Length))),
                 "Restore stack pointer after register restoration")

/// Generate RISC-V assembly for the given AST, using the given number of registers.
let codegen (node: TypedAST) (registers: uint): RISCV.Asm =
    /// Name of a special variable used to hold the result of the program
    let resultVarName = "$result"
    /// Initial codegen environment, with all registers available
    /// Note: the definition of 'env' uses list comprehension:
    /// https://en.wikibooks.org/wiki/F_Sharp_Programming/Lists#Using_List_Comprehensions
    let env = { TargetVar = resultVarName
                Frame = Map[(resultVarName, 0)]
                FrameSize = 1
                IntVarsInRegs = []
                FloatVarsInRegs = []
                FreeRegs = { Int = [for i in 0u..(registers - 1u) do yield Reg.r(i)]
                             Float = [for i in 0u..(registers - 1u) do yield FPReg.r(i)] }
                NeededVars = Set[resultVarName] }
    let result = doCodegen env node
    Asm(RV.MV(Reg.fp, Reg.sp), "Initialize frame pointer")
    ++ result.Asm
        .AddText([
            (RV.LI(Reg.a7, 10), "RARS syscall: Exit")
            (RV.ECALL, "Successful exit with code 0")
        ])
