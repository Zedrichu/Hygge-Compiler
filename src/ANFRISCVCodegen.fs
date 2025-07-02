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
let rec internal allocateIntVar (env: ANFCodegenEnv) (varName: string) : Reg * ANFCodegenResult =
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
                      (doNotSpill: List<string>): List<Reg> * ANFCodegenResult =
    /// List of variable names and types in the 'vars' AST nodes
    let varNamesTypes = List.map getVarNameAndType vars
    /// List of variable names in the 'vars' AST nodes
    let varNames = getVarNames vars

    /// Folder function that accumulates the codegen to load variables
    let loader (regs: List<Reg>, codegenRes: ANFCodegenResult) (vname, tpe) =
        match tpe with
        | TInt ->
            /// Register and codegen result after loading variable 'vname'. When
            /// loading the variable, we ensure that none of the variables in
            /// 'vars' is spilled
            let reg, loadRes = loadIntVar codegenRes.Env vname
                                            (doNotSpill @ varNames)
            (regs @ [reg],
             {codegenRes with Env = loadRes.Env
                              Asm = codegenRes.Asm ++ loadRes.Asm})
        | t -> failwith $"BUG: unsupported variable type %O{t}"

    List.fold loader ([], {Asm = Asm(); Env = env}) varNamesTypes


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
    // Variables loaded in a register in 'toEnv'
    let toIntVarsInRegs = Set.ofList (fst (List.unzip toEnv.IntVarsInRegs))

    /// Variables loaded in a register in 'toEnv' but not in 'fromEnv'
    let varsToLoad = Set.filter (fun v -> not (fromIntVarsInRegs.Contains v))
                                toIntVarsInRegs
    /// Variables loaded in a register in 'fromEnv' but not in 'toEnv'
    let varsToSpill = Set.filter (fun v -> not (toIntVarsInRegs.Contains v))
                                 fromIntVarsInRegs
    /// Is 'varName' loaded in different registers in 'fromEnv' and 'toEnv'?
    let needsReload (varName: string): bool =
        (Set.intersect fromIntVarsInRegs toIntVarsInRegs).Contains varName
            && (getIntVarRegister fromEnv varName) <> (getIntVarRegister toEnv varName)
    /// Variables loaded in different registers in 'fromEnv' and 'toEnv'
    let varsToReload = Set.filter needsReload toIntVarsInRegs

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
            | t -> failwith $"BUG: unsupported init expression type %O{t}"
        /// Cleaned-up codegen environment reduced to the variables that are
        /// actually used in the 'let' scope
        let scopeEnv =
            cleanupUnusedVars {initRes.Env with NeededVars = env.NeededVars
                                                TargetVar = env.TargetVar }
                              (ASTUtil.freeVars scope)
        /// Code generation for the 'let' scope
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
    | Var _ -> doCodegen env init

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
        | [lhsReg; rhsReg], argLoadRes ->
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
        | x ->
            failwith $"BUG: unexpected return value from 'loadVars': %O{x}"

    | Eq(lhs, rhs)
    | Less(lhs, rhs)
    | LessEq(lhs, rhs)
    | Greater(lhs, rhs)
    | GreaterEq(lhs, rhs) as expr when (expandType lhs.Env lhs.Type) = TInt ->
        /// Names of the variables used by the lhs and rhs of this operation
        let lrVarNames = getVarNames [lhs; rhs]
        match (loadVars env [lhs; rhs] []) with
        | [lhsReg; rhsReg], argLoadRes ->
            /// Target register to store the operation result + code to load it
            let targetReg, targetLoadRes =
                loadIntVar argLoadRes.Env env.TargetVar lrVarNames
            /// Human-readable prefix for jump labels, describing the kind of
            /// relational operation we are compiling
            let labelName = match expr with
                            | Eq _ -> "eq"
                            | Less _ -> "less"
                            | LessEq _ -> "less_eq"
                            | Greater _ -> "greater"
                            | GreaterEq _ -> "greater_eq"
                            | x -> failwith $"BUG: unexpected operation %O{x}"
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
        | x ->
            failwith $"BUG: unexpected return value from 'loadVars': %O{x}"
    
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
            let boolPrintCode = argLoadRes.Asm
                                    .AddData(strTrue, Alloc.String("true"))
                                    .AddData(strFalse, Alloc.String("false"))
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
            { Asm = argLoadRes.Asm ++ boolPrintCode
              Env = argLoadRes.Env }
        | TInt ->
            /// Printout code for integer variables
            let intPrintCode = argLoadRes.Asm
                                    .AddText([
                                        (RV.MV(Reg.a0, argReg), "Copy to a0 for printing")
                                        (RV.LI(Reg.a7, 1), "RARS syscall: PrintInt")
                                        (RV.ECALL, "")
                                    ])
            { Asm = argLoadRes.Asm ++ intPrintCode
              Env = argLoadRes.Env }
        | TString ->
            /// Printout code for string variables
            let stringPrintCode = argLoadRes.Asm
                                    .AddText([
                                        (RV.MV(Reg.a0, argReg), "Copy to a0 for printing")
                                        (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                                        (RV.ECALL, "")
                                    ])
            { Asm = argLoadRes.Asm ++ stringPrintCode
              Env = argLoadRes.Env }
        | t -> failwith $"BUG: Print codegen invoked on unsupported type %O{t}"
        | TFloat -> { Asm = Asm()
                      Env = env }
        

    | PrintLn(arg) ->
        /// Recycle codegen for Print above, then also output a newline token
        let printRes = doLetInitCodegen env { init with Expr = Print(arg) }
        
        /// Add the newline character
        let newlineAsm = Asm([
            (RV.LI(Reg.a0, int('\n')), "Character to print (newline)")
            (RV.LI(Reg.a7, 11), "RARS syscall: PrintChar")
            (RV.ECALL, "")
        ])
        
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
        /// Label to mark the end of the if..then...else code
        let labelEnd = Util.genSymbol "if_end"

        /// Assembly code for the whole 'if' expression. NOTE: this code
        /// generation is simplified, and it fails if the address of
        /// 'labelFalse' or 'labelEnd' is more than 2048 bytes far from the
        /// corresponding J instructions. A better approach would be to load the
        /// label into a register (using the instruction LA) and then jump using
        /// the instruction JR: this would be similar to the 'if' compilation in
        /// RISCVCodegen.fs ---  but this approach would consume one additional
        /// register, and possibly require the spilling of a variable
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
          Env = falseCodegenRes.Env }

    | _ ->
        failwith ($"BUG: unsupported AST node for 'let' init, maybe not in ANF:%s{Util.nl}"
                  + $"%s{PrettyPrinter.prettyPrint init}")


/// Generate RISC-V assembly for the given AST, using the given number of
/// registers.
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
