// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Functions to generate RISC-V assembly code from a typed Hygge AST.
module RISCVCodegen

open AST
open PrettyPrinter
open RISCV
open Type
open Typechecker


/// Exit code used in the generated assembly to signal an assertion violation.
let assertExitCode = 42 // Must be non-zero


/// Storage information for variables.
[<RequireQualifiedAccess; StructuralComparison; StructuralEquality>]
type internal Storage =
    /// The variable is stored in an integer register.
    | Reg of reg: Reg
    /// The variable is stored in a floating-point register.
    | FPReg of fpreg: FPReg
    /// The variable is stored in memory, in a location marked with a
    /// label in the compiled assembly code.
    | Label of label: string
    /// The variable is stored in the stack, at `offset` (bytes) from
    /// the memory address contained in the frame pointer register (fp).
    | Frame of offset: int


/// Code generation environment.
type internal CodegenEnv = {
    /// Target register number for the result of non-floating-point expressions.
    Target: uint
    /// Target register number for the result of floating-point expressions.
    FPTarget: uint
    /// Storage information about known variables.
    VarStorage: Map<string, Storage>
    /// Binary flag indicating if active environment is at program top-level.
    TopLevel: bool
}

/// Function to add a variable into the environment of the node recursively.
let rec internal addVarNode (node: Node<TypingEnv, Type>) (var: string) (tpe: Type) =
    match node.Expr with
    | UnitVal
    | BoolVal _
    | IntVal _
    | FloatVal _
    | StringVal _
    | ReadInt
    | ReadFloat
    | Var _ -> {node with Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Sqrt arg -> {node with Expr = Sqrt (addVarNode arg var tpe)
                             Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Add(lhs, rhs) -> {node with Expr = Add (addVarNode lhs var tpe,
                                              addVarNode rhs var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Sub(lhs, rhs) -> {node with Expr = Sub (addVarNode lhs var tpe,
                                              addVarNode rhs var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Mult(lhs, rhs) -> {node with Expr = Mult (addVarNode lhs var tpe,
                                                addVarNode rhs var tpe)
                                   Env.Vars = node.Env.Vars.Add (var, tpe)}

    | Div(lhs, rhs) -> {node with Expr = Div (addVarNode lhs var tpe,
                                              addVarNode rhs var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Mod(lhs, rhs) -> {node with Expr = Mod (addVarNode lhs var tpe,
                                              addVarNode rhs var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Min(lhs, rhs) -> {node with Expr = Min (addVarNode lhs var tpe,
                                              addVarNode rhs var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Max(lhs, rhs) -> {node with Expr = Max (addVarNode lhs var tpe,
                                              addVarNode rhs var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | And(lhs, rhs) -> {node with Expr = And (addVarNode lhs var tpe,
                                              addVarNode rhs var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Or(lhs, rhs) -> {node with Expr = Or (addVarNode lhs var tpe,
                                            addVarNode rhs var tpe)
                                 Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Not arg -> {node with Expr = Not (addVarNode arg var tpe)
                            Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Eq(lhs, rhs) -> {node with Expr = Eq (addVarNode lhs var tpe,
                                            addVarNode rhs var tpe)
                                 Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Less(lhs, rhs) -> {node with Expr = Less (addVarNode lhs var tpe,
                                                addVarNode rhs var tpe)
                                   Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Greater(lhs, rhs) -> {node with Expr = Greater (addVarNode lhs var tpe,
                                                      addVarNode rhs var tpe)
                                      Env.Vars = node.Env.Vars.Add (var, tpe)}
    | LessEq(lhs, rhs) -> {node with Expr = LessEq (addVarNode lhs var tpe,
                                                    addVarNode rhs var tpe)
                                     Env.Vars = node.Env.Vars.Add (var, tpe)}
    | GreaterEq(lhs, rhs) -> {node with Expr = GreaterEq (addVarNode lhs var tpe,
                                                          addVarNode rhs var tpe)
                                        Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Print arg -> {node with Expr = Print (addVarNode arg var tpe)
                              Env.Vars = node.Env.Vars.Add (var, tpe)}
    | PrintLn arg -> {node with Expr = PrintLn (addVarNode arg var tpe)
                                Env.Vars = node.Env.Vars.Add (var, tpe)}
    | If(condition, ifTrue, ifFalse) -> {node with Expr = If (addVarNode condition var tpe,
                                                              addVarNode ifTrue var tpe,
                                                              addVarNode ifFalse var tpe)
                                                   Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Seq nodes -> let newNodes = List.map (fun n -> addVarNode n var tpe) nodes
                   {node with Expr = Seq newNodes
                              Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Type(name, def, scope) -> {node with Expr = Type(name, def, addVarNode scope var tpe)
                                           Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Ascription(tpea, node) -> {node with Expr = Ascription(tpea, addVarNode node var tpe)
                                           Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Assertion arg -> {node with Expr = Assertion (addVarNode arg var tpe)
                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Let(name, init, scope) -> {node with Expr = Let(name, addVarNode init var tpe,
                                                            addVarNode scope var tpe)
                                           Env.Vars = node.Env.Vars.Add (var, tpe)}
    | LetT(name, tpen, init, scope) -> {node with Expr = LetT(name, tpen, addVarNode init var tpe,
                                                                          addVarNode scope var tpe)
                                                  Env.Vars = node.Env.Vars.Add (var, tpe)}
    | LetRec(name, tpen, init, scope) -> {node with Expr = LetRec(name, tpen, addVarNode init var tpe,
                                                                              addVarNode scope var tpe)
                                                    Env.Vars = node.Env.Vars.Add (var, tpe)}
    | LetMut(name, init, scope) -> {node with Expr = LetMut(name, addVarNode init var tpe,
                                                                  addVarNode scope var tpe)
                                              Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Assign(target, expr) -> {node with Expr = Assign(addVarNode target var tpe,
                                                       addVarNode expr var tpe)
                                         Env.Vars = node.Env.Vars.Add (var, tpe)}
    | While(cond, body) -> {node with Expr = While(addVarNode cond var tpe,
                                                   addVarNode body var tpe)
                                      Env.Vars = node.Env.Vars.Add (var, tpe)}
    | DoWhile(body, cond) -> {node with Expr = DoWhile(addVarNode body var tpe,
                                                       addVarNode cond var tpe)
                                        Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Lambda(args, body) -> {node with Expr = Lambda(args, addVarNode body var tpe)
                                       Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Application(expr, args) -> {node with Expr = Application(addVarNode expr var tpe,
                                                    List.map (fun arg -> addVarNode arg var tpe) args)
                                            Env.Vars = node.Env.Vars.Add (var, tpe)}
    | StructCons fields -> {node with Expr = StructCons (List.map (fun (name, expr) -> name, addVarNode expr var tpe) fields)
                                      Env.Vars = node.Env.Vars.Add (var, tpe)}
    | FieldSelect(target, field) -> {node with Expr = FieldSelect(addVarNode target var tpe, field)
                                               Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Pointer addr -> {node with Expr = Pointer addr
                                 Env.Vars = node.Env.Vars.Add (var, tpe)}
    | ArrayCons(length, init) -> {node with Expr = ArrayCons(length, addVarNode init var tpe)
                                            Env.Vars = node.Env.Vars.Add (var, tpe)}
    | ArrayLength target -> {node with Expr = ArrayLength(addVarNode target var tpe)
                                       Env.Vars = node.Env.Vars.Add (var, tpe)}
    | ArrayElem(target, index) -> {node with Expr = ArrayElem(addVarNode target var tpe,
                                                              addVarNode index var tpe)
                                             Env.Vars = node.Env.Vars.Add (var, tpe)}
    | ArraySlice(target, startIdx, endIdx) -> {node with Expr = ArraySlice(addVarNode target var tpe,
                                                                           addVarNode startIdx var tpe,
                                                                           addVarNode endIdx var tpe)
                                                         Env.Vars = node.Env.Vars.Add (var, tpe)}
    | UnionCons(label, expr) -> {node with Expr = UnionCons(label, addVarNode expr var tpe)
                                           Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Match(expr, cases) -> {node with Expr = Match(addVarNode expr var tpe,
                                                List.map (fun (label, name, body) ->
                                                    label, name, addVarNode body var tpe) cases)
                                       Env.Vars = node.Env.Vars.Add (var, tpe)}
    | Copy arg -> {node with Expr = Copy(addVarNode arg var tpe)
                             Env.Vars = node.Env.Vars.Add (var, tpe)}
    
/// Code generation function: compile the expression in the given AST node so
/// that it writes its results on the 'Target' and 'FPTarget' generic register
/// numbers (specified in the given codegen 'env'ironment).  IMPORTANT: the
/// generated code must never modify the contents of register numbers lower than
/// the given targets.
let rec internal doCodegen (env: CodegenEnv) (node: TypedAST): Asm =
    match node.Expr with
    | UnitVal -> Asm() // Nothing to do

    | BoolVal(v) ->
        /// Boolean constant turned into integer 1 if true, or 0 if false
        let value = if v then 1 else 0
        Asm(RV.LI(Reg.r(env.Target), value), $"Bool value '%O{v}'")

    | IntVal(v) ->
        Asm(RV.LI(Reg.r(env.Target), v))

    | FloatVal(v) ->
        // We convert the float value into its bytes, and load it as immediate
        let bytes = System.BitConverter.GetBytes(v)
        if (not System.BitConverter.IsLittleEndian)
            then System.Array.Reverse(bytes) // RISC-V is little-endian
        let word: int32 = System.BitConverter.ToInt32(bytes)

        // Current handling of floats writes bytes to t0 then to fpreg, but we use t0 to store the function address.
        // Solution: We save the contents of the env.Target register before using it to perform the conversion, then it is restored after the float val is loaded into FP reg.
        Asm([ (RV.ADDI(Reg.sp, Reg.sp, Imm12(-4)), "Allocate stack space to save register") // RARS commenting for debugging... if it's annoying you can remove it.
              (RV.SW(Reg.r(env.Target), Imm12(0), Reg.sp), "Save env.Target register to stack")
              (RV.LI(Reg.r(env.Target), word), $"Float value %f{v}")
              (RV.FMV_W_X(FPReg.r(env.FPTarget), Reg.r(env.Target)), $"Move float value %f{v} to FP register")
              (RV.LW(Reg.r(env.Target), Imm12(0), Reg.sp), "Restore env.Target register from stack")
              (RV.ADDI(Reg.sp, Reg.sp, Imm12(4)), "Deallocate stack space") ])
    
    | StringVal(v) ->
        // Label marking the string constant in the data segment
        let label = Util.genSymbol "string_val"
        Asm().AddData(label, Alloc.String(v)) // instead of Alloc.String(v)
             .AddText(RV.LA(Reg.r(env.Target), label))

    | Var(name) ->
        // To compile a variable, we inspect its type and where it is stored
        match node.Type with
        | t when (isSubtypeOf node.Env t TUnit)
            -> Asm() // A unit-typed variable is just ignored
        | t when (isSubtypeOf node.Env t TFloat) ->
            match (env.VarStorage.TryFind name) with
            | Some(Storage.FPReg(fpreg)) ->
                Asm(RV.FMV_S(FPReg.r(env.FPTarget), fpreg),
                    $"Load variable '%s{name}'")
            | Some(Storage.Label(lab)) ->
                Asm([ (RV.LA(Reg.r(env.Target), lab),
                       $"Load address of variable '%s{name}'")
                      (RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target)),
                       $"Load value of variable '%s{name}'")
                      (RV.FMV_W_X(FPReg.r(env.FPTarget), Reg.r(env.Target)),
                       $"Transfer '%s{name}' to fp register") ])
            | Some(Storage.Frame(offset)) ->
                Asm(RV.FLW_S(FPReg.r(env.FPTarget), Imm12(offset), Reg.fp),
                $"Load float variable '%s{name}' from stack at offset %d{offset}")
            | Some(Storage.Reg(_)) as st ->
                failwith $"BUG: variable %s{name} of type %O{t} has unexpected storage %O{st}"
            | None -> failwith $"BUG: float variable without storage: %s{name}"
        | t ->  // Default case for variables holding integer-like values
            match (env.VarStorage.TryFind name) with
            | Some(Storage.Reg(reg)) ->
                Asm(RV.MV(Reg.r(env.Target), reg), $"Load variable '%s{name}'")
            | Some(Storage.Label(lab)) ->
                // No distinction between TFun and other vars as function objs are closure environment structs
                Asm([ (RV.LA(Reg.r(env.Target), lab),
                       $"Load label address of variable '%s{name}'")
                      (RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target)),
                       $"Load value of variable '%s{name}'") ])
            | Some(Storage.Frame(offset)) ->
                Asm(RV.LW(Reg.r(env.Target), Imm12(offset), Reg.fp),
                $"Load variable '%s{name}' from stack at offset %d{offset}, with fp at %d{Reg.fp.Number}")
            | Some(Storage.FPReg(_)) as st ->
                failwith $"BUG: variable %s{name} of type %O{t} has unexpected storage %O{st}"
            | None -> failwith $"BUG: variable without storage: %s{name}"

    | Add(lhs, rhs)
    | Sub(lhs, rhs)
    | Div(lhs, rhs)
    | Mod(lhs, rhs)
    | Max(lhs, rhs)
    | Min(lhs, rhs)
    | Mult(lhs, rhs) as expr ->
        // Code generation for addition and multiplication is very
        // similar: we compile the lhs and rhs giving them different target
        // registers, and then apply the relevant assembly operation(s) on their
        // results.

        /// Generated code for the lhs expression
        let lAsm = doCodegen env lhs
        // The generated code depends on the type of addition being computed
        match node.Type with
        | t when (isSubtypeOf node.Env t TInt) ->
            /// Target register for the rhs expression
            let rtarget = env.Target + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with Target = rtarget} rhs
            let label = Util.genSymbol "minmax_done"
            /// Generated code for the numerical operation
            let opAsm =
                match expr with
                    | Add(_,_) ->
                        Asm(RV.ADD(Reg.r(env.Target),
                                   Reg.r(env.Target), Reg.r(rtarget)))
                    | Sub(_,_) ->
                        Asm(RV.SUB(Reg.r(env.Target),
                                   Reg.r(env.Target), Reg.r(rtarget)))
                    | Mult(_,_) ->
                        Asm(RV.MUL(Reg.r(env.Target),
                                   Reg.r(env.Target), Reg.r(rtarget)))
                    | Div(_,_) ->
                        Asm(RV.DIV(Reg.r(env.Target),
                                   Reg.r(env.Target), Reg.r(rtarget)))
                    | Mod(_,_) ->
                        Asm(RV.REM(Reg.r(env.Target),
                                   Reg.r(env.Target), Reg.r(rtarget)))
                    | Min(_,_) -> Asm().AddText([
                            (RV.BLT(Reg.r(env.Target), Reg.r(rtarget), label), "")
                            (RV.MV(Reg.r(env.Target), Reg.r(rtarget)), "")
                            (RV.LABEL(label), "")
                        ])
                    | Max(_,_) -> Asm().AddText([
                            (RV.BLT(Reg.r(rtarget), Reg.r(env.Target), label), "")
                            (RV.MV(Reg.r(env.Target), Reg.r(rtarget)), "")
                            (RV.LABEL(label), "")
                        ])
                    | x -> failwith $"BUG: unexpected operation %O{x}"
            // Put everything together
            lAsm ++ rAsm ++ opAsm
        | t when (isSubtypeOf node.Env t TFloat) ->
            /// Target register for the rhs expression
            let rfptarget = env.FPTarget + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with FPTarget = rfptarget} rhs
            let label = Util.genSymbol "minmax_done"
            /// Generated code for the numerical operation
            let opAsm =
                match expr with
                | Add(_,_) ->
                    Asm(RV.FADD_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | Sub(_,_) ->
                    Asm(RV.FSUB_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | Mult(_,_) ->
                    Asm(RV.FMUL_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | Div(_,_) ->
                    Asm(RV.FDIV_S(FPReg.r(env.FPTarget),
                                  FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | Min(_,_) ->
                    Asm(RV.FLT_S(Reg.r(env.Target), FPReg.r(rfptarget), FPReg.r(env.FPTarget))) ++
                    Asm(RV.BEQ(Reg.r(env.Target), Reg.zero, label)) ++
                    Asm(RV.FMV_S(FPReg.r(env.FPTarget), FPReg.r(rfptarget))) ++
                    Asm(RV.LABEL(label))
                | Max(_,_) ->
                    Asm(RV.FLT_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget))) ++
                    Asm(RV.BEQ(Reg.r(env.Target), Reg.zero, label)) ++
                    Asm(RV.FMV_S(FPReg.r(env.FPTarget), FPReg.r(rfptarget))) ++
                    Asm(RV.LABEL(label))
                | x -> failwith $"BUG: unexpected operation %O{x}"
            // Put everything together
            lAsm ++ rAsm ++ opAsm
        | t ->
            failwith $"BUG: numerical operation codegen invoked on invalid type %O{t}"

    | Sqrt(arg) ->
        // Generate code for the argument expression
        let argAsm = doCodegen env arg

        let opAsm =
            match arg.Type with
            | TFloat ->
                Asm(RV.FSQRT_S(FPReg.r(env.FPTarget), FPReg.r(env.FPTarget)))

            | TInt ->
                Asm(RV.FCVT_S_W(FPReg.r(env.FPTarget), Reg.r(env.Target))) ++
                Asm(RV.FSQRT_S(FPReg.r(env.FPTarget), FPReg.r(env.FPTarget)))
            | _ -> failwith $"BUG: sqrt operation codegen invoked on invalid type %O{arg.Type}"

        argAsm ++ opAsm


    | And(lhs, rhs)
    | Or(lhs, rhs) as expr ->
        // Code generation for logical 'and' and 'or' is very similar: we
        // compile the lhs and rhs giving them different target registers, and
        // then apply the relevant assembly operation(s) on their results.

        /// Generated code for the lhs expression
        let lAsm = doCodegen env lhs
        /// Target register for the rhs expression
        let rtarget = env.Target + 1u
        /// Generated code for the rhs expression
        let rAsm = doCodegen {env with Target = rtarget} rhs
        /// Generated code for the logical operation
        let opAsm =
            match expr with
            | And(_,_) ->
                Asm(RV.AND(Reg.r(env.Target), Reg.r(env.Target), Reg.r(rtarget)))
            | Or(_,_) ->
                Asm(RV.OR(Reg.r(env.Target), Reg.r(env.Target), Reg.r(rtarget)))
            | x -> failwith $"BUG: unexpected operation %O{x}"
        // Put everything together
        lAsm ++ rAsm ++ opAsm

    | Not(arg) ->
        /// Generated code for the argument expression (note that we don't need
        /// to increase its target register)
        let asm = doCodegen env arg
        asm.AddText(RV.SEQZ(Reg.r(env.Target), Reg.r(env.Target)))

    | Eq(lhs, rhs)
    | Less(lhs, rhs)
    | LessEq(lhs, rhs)
    | Greater(lhs, rhs)
    | GreaterEq(lhs, rhs) as expr ->
        // Code generation for equality and less-than relations is very similar:
        // we compile the lhs and rhs giving them different target registers,
        // and then apply the relevant assembly operation(s) on their results.

        /// Generated code for the lhs expression
        let lAsm = doCodegen env lhs
        // The generated code depends on the lhs and rhs types
        match lhs.Type with
        | t when (isSubtypeOf lhs.Env t TInt) ->
            // Our goal is to write 1 (true) or 0 (false) in the register
            // env.Target, depending on the result of the comparison between
            // the lhs and rhs.  To achieve this, we perform a conditional
            // branch depending on whether the lhs and rhs are equal (or the lhs
            // is less than the rhs):
            // - if the comparison is true, we jump to a label where we write
            //   1 in the target register, and continue
            // - if the comparison is false, we write 0 in the target register
            //   and we jump to a label marking the end of the generated code

            /// Target register for the rhs expression
            let rtarget = env.Target + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with Target = rtarget} rhs

            /// Human-readable prefix for jump labels, describing the kind of
            /// relational operation we are compiling
            let labelName = match expr with
                            | Eq(_,_) -> "eq"
                            | Less(_,_) -> "less"
                            | LessEq(_,_) -> "lesseq"
                            | Greater(_,_) -> "greater"
                            | GreaterEq(_,_) -> "greatereq"
                            | x -> failwith $"BUG: unexpected operation %O{x}"
            /// Label to jump to when the comparison is true
            let trueLabel = Util.genSymbol $"%O{labelName}_true"
            /// Label to mark the end of the comparison code
            let endLabel = Util.genSymbol $"%O{labelName}_end"

            /// Codegen for the relational operation between lhs and rhs
            let opAsm =
                match expr with
                | Eq(_,_) ->
                    Asm(RV.BEQ(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | Less(_,_) ->
                    Asm(RV.BLT(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | LessEq(_,_) ->
                    Asm(RV.BLE(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | Greater(_,_) ->
                    Asm(RV.BGT(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | GreaterEq(_,_) ->
                    Asm(RV.BGE(Reg.r(env.Target), Reg.r(rtarget), trueLabel))
                | x -> failwith $"BUG: unexpected operation %O{x}"

            // Put everything together
            (lAsm ++ rAsm ++ opAsm)
                .AddText([
                    (RV.LI(Reg.r(env.Target), 0), "Comparison result is false")
                    (RV.J(endLabel), "")
                    (RV.LABEL(trueLabel), "")
                    (RV.LI(Reg.r(env.Target), 1), "Comparison result is true")
                    (RV.LABEL(endLabel), "")
                ])
        | t when (isSubtypeOf lhs.Env t TFloat) ->
            /// Target register for the rhs expression
            let rfptarget = env.FPTarget + 1u
            /// Generated code for the rhs expression
            let rAsm = doCodegen {env with FPTarget = rfptarget} rhs
            /// Generated code for the relational operation
            let opAsm =
                match expr with
                | Eq(_,_) ->
                    Asm(RV.FEQ_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | Less(_,_) ->
                    Asm(RV.FLT_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | LessEq(_,_) ->
                    Asm(RV.FLE_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | Greater(_,_) ->
                    Asm(RV.FGT_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | GreaterEq(_,_) ->
                    Asm(RV.FGE_S(Reg.r(env.Target), FPReg.r(env.FPTarget), FPReg.r(rfptarget)))
                | x -> failwith $"BUG: unexpected operation %O{x}"
            // Put everything together
            (lAsm ++ rAsm ++ opAsm)
        | t ->
            failwith $"BUG: relational operation codegen invoked on invalid type %O{t}"

    | ReadInt ->
        (beforeSysCall [Reg.a0] [])
            .AddText([
                (RV.LI(Reg.a7, 5), "RARS syscall: ReadInt")
                (RV.ECALL, "")
                (RV.MV(Reg.r(env.Target), Reg.a0), "Move syscall result to target")
            ])
            ++ (afterSysCall [Reg.a0] [])

    | ReadFloat ->
        (beforeSysCall [] [FPReg.fa0])
            .AddText([
                (RV.LI(Reg.a7, 6), "RARS syscall: ReadFloat")
                (RV.ECALL, "")
                (RV.FMV_S(FPReg.r(env.FPTarget), FPReg.fa0), "Move syscall result to target")
            ])
            ++ (afterSysCall [] [FPReg.fa0])

    | Print(arg) ->
        /// Compiled code for the 'print' argument, leaving its result on the
        /// generic register 'target' or 'fptarget' (depending on its type)
        let argCode = doCodegen env arg
        // The generated code depends on the 'print' argument type
        match arg.Type with
        | t when (isSubtypeOf arg.Env t TBool) ->
            let strTrue = Util.genSymbol "true"
            let strFalse = Util.genSymbol "false"
            let printFalse = Util.genSymbol "print_true"
            let printExec = Util.genSymbol "print_execute"
            argCode.AddData(strTrue, Alloc.String("true"))
                .AddData(strFalse, Alloc.String("false"))
                ++ (beforeSysCall [Reg.a0] [])
                  .AddText([
                    (RV.BEQZ(Reg.r(env.Target), printFalse), "")
                    (RV.LA(Reg.a0, strTrue), "String to print via syscall")
                    (RV.J(printExec), "")
                    (RV.LABEL(printFalse), "")
                    (RV.LA(Reg.a0, strFalse), "String to print via syscall")
                    (RV.LABEL(printExec), "")
                    (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                    (RV.ECALL, "")
                  ])
                  ++ (afterSysCall [Reg.a0] [])
        | t when (isSubtypeOf arg.Env t TInt) ->
            argCode
            ++ (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.MV(Reg.a0, Reg.r(env.Target)), "Copy to a0 for printing")
                    (RV.LI(Reg.a7, 1), "RARS syscall: PrintInt")
                    (RV.ECALL, "")
                ])
                ++ (afterSysCall [Reg.a0] [])
        | t when (isSubtypeOf arg.Env t TFloat) ->
            argCode
            ++ (beforeSysCall [] [FPReg.fa0])
                .AddText([
                    (RV.FMV_S(FPReg.fa0, FPReg.r(env.FPTarget)), "Copy to fa0 for printing")
                    (RV.LI(Reg.a7, 2), "RARS syscall: PrintFloat")
                    (RV.ECALL, "")
                ])
                ++ (afterSysCall [] [FPReg.fa0])
        | t when (isSubtypeOf arg.Env t TString) ->
            argCode
            ++ (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.MV(Reg.a0, Reg.r(env.Target)), "Copy to a0 for printing")
                    (RV.LI(Reg.a7, 4), "RARS syscall: PrintString")
                    (RV.ECALL, "")
                ])
                ++ (afterSysCall [Reg.a0] [])
        | t ->
            match expandType arg.Env t with
            | TStruct fields ->
                let nodes = 
                    [{ node with Expr = Print({ node with Expr = StringVal("struct { "); Type = TString }) }] @
                    (List.collect (fun (name, tpe) ->
                        let strVals = 
                            match tpe with
                            | TString -> (name + @" = \"""), @"\""; "
                            | _ -> (name + " = "), "; "
                        [
                            { node with Expr = Print({ node with Expr = StringVal(fst strVals); Type = TString }) }
                            { node with Expr = Print({ node with Expr = FieldSelect(arg, name); Type = tpe }) }
                            { node with Expr = Print({ node with Expr = StringVal(snd strVals); Type = TString }) }
                        ]
                    ) fields) @
                    [{ node with Expr = Print({ node with Expr = StringVal("}"); Type = TString }) }]
                doCodegen env { node with Expr = Seq(nodes) }
            | TArray tpe ->
                let nodes = [
                    { node with Expr = Print({ node with Expr = StringVal($"Array{{ type: {tpe.ToString()}; length: "); Type = TString }) }
                    { node with Expr = Print({ node with Expr = ArrayLength(arg); Type = TInt }) }
                    { node with Expr = Print({ node with Expr = StringVal(" }"); Type = TString }) }
                ]
                doCodegen env { node with Expr = Seq(nodes) }
            | TFun (args, ret) ->
                // let args' = List.map (fun (e: Type) -> e.ToString()) args |> String.concat ", "
                let nodes = [
                    { node with Expr = Print({ node with Expr = StringVal(t.ToString()); Type = TString }) }
                    // { node with Expr = Print({ node with Expr = StringVal(ret.ToString() + " }"); Type = TString }) }
                ]
                doCodegen env { node with Expr = Seq(nodes) }
            | exp_t ->
                failwith $"BUG: Print codegen invoked on unsupported type %O{exp_t} (original: %O{t})"

    | PrintLn(arg) ->
        // Recycle codegen for Print above, then also output a newline
        (doCodegen env {node with Expr = Print(arg)})
        ++ (beforeSysCall [Reg.a0] [])
            .AddText([
                (RV.LI(Reg.a7, 11), "RARS syscall: PrintChar")
                (RV.LI(Reg.a0, int('\n')), "Character to print (newline)")
                (RV.ECALL, "")
            ])
            ++ (afterSysCall [Reg.a0] [])

    | If(condition, ifTrue, ifFalse) ->
        /// Label to jump to when the 'if' condition is true
        let labelTrue = Util.genSymbol "if_true"
        /// Label to jump to when the 'if' condition is false
        let labelFalse = Util.genSymbol "if_false"
        /// Label to mark the end of the if..then...else code
        let labelEnd = Util.genSymbol "if_end"
        // Compile the 'if' condition; if the result is true (i.e., not zero)
        // then jump to 'labelTrue', execute the 'ifTrue' code, and finally jump
        // to 'labelEnd' (thus skipping the code under 'labelFalse'). Otherwise
        // (i.e., when the 'if' condition result is false) jump to 'labelFalse'
        // and execute the 'ifFalse' code. Here we use a register to load the
        // address of a label (using the instruction LA) and then jump to it
        // (using the instruction JR): this way, the label address can be very
        // far from the jump instruction address --- and this can be important
        // if the compilation of 'ifTrue' and/or 'ifFalse' produces a large
        // amount of assembly code
        (doCodegen env condition)
            .AddText([ (RV.BNEZ(Reg.r(env.Target), labelTrue),
                        "Jump when 'if' condition is true")
                       (RV.LA(Reg.r(env.Target), labelFalse),
                        "Load the address of the 'false' branch of the 'if' code")
                       (RV.JR(Reg.r(env.Target)),
                        "Jump to the 'false' branch of the 'if' code")
                       (RV.LABEL(labelTrue),
                        "Beginning of the 'true' branch of the 'if' code") ])
            ++ (doCodegen env ifTrue)
                .AddText([ (RV.LA(Reg.r(env.Target + 1u), labelEnd),
                            "Load the address of the end of the 'if' code")
                           (RV.JR(Reg.r(env.Target + 1u)),
                            "Jump to skip the 'false' branch of 'if' code")
                           (RV.LABEL(labelFalse),
                            "Beginning of the 'false' branch of the 'if' code") ])
                ++ (doCodegen env ifFalse)
                    .AddText(RV.LABEL(labelEnd), "End of the 'if' code")

    | Seq(nodes) ->
        // We collect the code of each sequence node by folding over all nodes
        let folder (asm: Asm) (node: TypedAST) =
            asm ++ (doCodegen env node)
        List.fold folder (Asm()) nodes

    | Type(_, _, scope) ->
        // A type alias does not produce any code --- but its scope does
        doCodegen env scope

    | Ascription(_, node) ->
        // A type ascription does not produce code --- but the type-annotated
        // AST node does
        doCodegen env node

    | Assertion(arg) ->
        /// Label to jump to when the assertion is true
        let passLabel = Util.genSymbol "assert_true"

        // Reconstruct the AST to do a printout and then exit as usual for assertion - from Parser

        // Check the assertion, and jump to 'passLabel' if it is true;
        // otherwise, fail
        (doCodegen env arg)
            // .AddData([])
            .AddText([
                (RV.ADDI(Reg.r(env.Target), Reg.r(env.Target), Imm12(-1)), "")
                (RV.BEQZ(Reg.r(env.Target), passLabel), "Jump if assertion OK")
                (RV.LI(Reg.a7, 93), "RARS syscall: Exit2")
                (RV.LI(Reg.a0, assertExitCode), "Assertion violation exit code")
                (RV.ECALL, "")
                (RV.LABEL(passLabel), "")
            ])

    // Special case for compiling a function with a given immutable name in the
    // input source file.  We recognise this case by checking whether the
    // 'Let...' declares 'name' as a Lambda expression with a TFun type
    | Let(name, {Node.Expr = Lambda(args, body);
                 Node.Type = TFun(targs, _)}, scope)
    | LetRec(name, _, {Node.Expr = Lambda(args, body);
                       Node.Type = TFun(targs, _)}, scope)
    | LetT(name, _, {Node.Expr = Lambda(args, body);
                     Node.Type = TFun(targs, _)}, scope) ->
        /// Assembly label to mark the position of the compiled function body.
        /// For readability, we make the label similar to the function name
        let funLabel = Util.genSymbol $"fun_%s{name}"

        /// Storage info where the name of the compiled function points to the closure environment
        let varStorage2 = env.VarStorage.Add(name, Storage.Reg(Reg.r(env.Target)))

        // Finally, compile the 'let...'' scope with the newly-defined function
        // label in the variables storage, and append the 'funCode' above. The
        // 'scope' code leaves its result in the 'let...' target register
        let scopeCode = doCodegen {env with VarStorage = varStorage2
                                            Target = env.Target + 1u } scope
        /// Perform closure conversion on the lambda term, for immutable variable closures
        let closureConversionCode = closureConversion env funLabel node (Some(name)) args targs body

        /// Move the result of the `let...` scope back to the target register
        let moveScopeResultCode = Asm(RV.MV(Reg.r(env.Target), Reg.r(env.Target + 1u)))

        closureConversionCode ++ scopeCode ++ moveScopeResultCode

    // Typechecking should ensure that a LetRec expression is always initialised with a lambda expression (see notes Module 6).
    | LetRec _ ->
        failwith $"BUG: unexpected LetRec node without lambda initialisation in codegen: %s{PrettyPrinter.prettyPrint node}"

    | Let(name, init, scope)
    | LetT(name, _, init, scope)
    | LetMut(name, init, scope) ->
        /// 'let...' initialisation code, which leaves its result in the
        /// 'target' register (which we overwrite at the end of the 'scope'
        /// execution)
        let initCode = doCodegen {env with TopLevel = false} init

        /// Label for potential top-level variables stored in the data segment.
        let label = Util.genSymbol $"label_var_{name}"

        /// Code to save top-level variables to a generated label of the data segment.
        let topLevelLabelCode (tpe: Type) =
            match env.TopLevel, tpe with
            | true, TFloat ->
                Asm()
                    .AddText([
                        RV.LA(Reg.r(env.Target), label),
                        "Load top-level variable label address"
                        RV.FSW_S(FPReg.r(env.FPTarget), Imm12(0), Reg.r(env.Target)),
                        "Save top-level variable value to data segment"
                    ])
                    .AddData(label, Alloc.Word(1))
            | true, _ ->
                Asm()
                    .AddText([
                        RV.LA(Reg.r(env.Target + 1u), label),
                        "Load top-level variable label address"
                        RV.SW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target + 1u)),
                        "Save top-level variable value to data segment"
                    ])
                    .AddData(label, Alloc.Word(1))
            | false, _ -> Asm()

        match init.Type with
        | t when (isSubtypeOf init.Env t TUnit) ->
            // The 'init' produces a unit value, i.e. nothing: we can keep using
            // the same target registers, and we don't need to update the
            // variables-to-registers mapping.
            initCode ++ (doCodegen env scope)
        | t when (isSubtypeOf init.Env t TFloat) ->
            /// Target register for compiling the 'let' scope
            let scopeTarget = env.FPTarget + 1u
            /// Variable storage for compiling the 'let' scope
            let scopeVarStorage =
                match env.TopLevel with
                | true -> env.VarStorage.Add(name, Storage.Label(label))
                | false -> env.VarStorage.Add(name, Storage.FPReg(FPReg.r(env.FPTarget)))

            /// Environment for compiling the 'let' scope
            let scopeEnv = { env with FPTarget = scopeTarget
                                      VarStorage = scopeVarStorage }
            initCode ++ (topLevelLabelCode t)
                ++ (doCodegen scopeEnv scope)
                    .AddText(RV.FMV_S(FPReg.r(env.FPTarget),
                                      FPReg.r(scopeTarget)),
                             "Move result of 'let' scope expression into target register")
        | _ ->  // Default case for integer-like initialisation expressions
            /// Target register for compiling the 'let' scope
            let scopeTarget = env.Target + 1u
            /// Variable storage for compiling the 'let' scope
            let scopeVarStorage =
                match env.TopLevel with
                | true -> env.VarStorage.Add(name, Storage.Label(label))
                | false -> env.VarStorage.Add(name, Storage.Reg(Reg.r(env.Target)))
            /// Environment for compiling the 'let' scope
            let scopeEnv = { env with Target = scopeTarget
                                      VarStorage = scopeVarStorage }
            initCode ++ (topLevelLabelCode init.Type)
                ++ (doCodegen scopeEnv scope)
                    .AddText(RV.MV(Reg.r(env.Target), Reg.r(scopeTarget)),
                             "Move 'let' scope result to 'let' target register")

    | Assign(lhs, rhs) ->
        match lhs.Expr with
        | Var(name) ->
            /// Code for the 'rhs', leaving its result in the target register
            let rhsCode = doCodegen env rhs
            match rhs.Type with
            | t when (isSubtypeOf rhs.Env t TUnit) ->
                rhsCode // No assignment to perform
            | _ ->
                match (env.VarStorage.TryFind name) with
                | Some(Storage.Reg(reg)) ->
                    rhsCode.AddText(RV.MV(reg, Reg.r(env.Target)),
                                    $"Assignment to variable %s{name}")
                | Some(Storage.FPReg(reg)) ->
                    rhsCode.AddText(RV.FMV_S(reg, FPReg.r(env.FPTarget)),
                                    $"Assignment to variable %s{name}")
                | Some(Storage.Label(lab)) ->
                    match rhs.Type with
                    | t when (isSubtypeOf rhs.Env t TFloat) ->
                        rhsCode.AddText([ (RV.LA(Reg.r(env.Target), lab),
                                           $"Load address of variable '%s{name}'")
                                          (RV.FSW_S(FPReg.r(env.FPTarget), Imm12(0),
                                                    Reg.r(env.Target)),
                                           $"Transfer value of '%s{name}' to memory") ])
                    | _ ->
                        rhsCode.AddText([ (RV.LA(Reg.r(env.Target + 1u), lab),
                                           $"Load address of variable '%s{name}'")
                                          (RV.SW(Reg.r(env.Target), Imm12(0),
                                                 Reg.r(env.Target + 1u)),
                                           $"Transfer value of '%s{name}' to memory") ])
                | Some(Storage.Frame(offset)) ->
                    match rhs.Type with
                    | t when (isSubtypeOf rhs.Env t TFloat) ->
                        rhsCode.AddText(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(offset), Reg.fp),
                        $"Assignment to float variable %s{name} on stack at offset %d{offset}")
                    | _ ->
                        rhsCode.AddText(RV.SW(Reg.r(env.Target), Imm12(offset), Reg.fp),
                        $"Assignment to variable %s{name} on stack at offset %d{offset}")
                | None -> failwith $"BUG: variable without storage: %s{name}"

        | FieldSelect(target, field) ->
            /// Assembly code for computing the 'target' object of which we are
            /// selecting the 'field'.  We write the computation result (which
            /// should be a struct memory address) in the target register.
            let selTargetCode = doCodegen env target
            /// Code for the 'rhs', leaving its result in the target+1 register
            let rhsCode = doCodegen {env with Target = env.Target + 1u} rhs
            match (expandType target.Env target.Type) with
            | TStruct(fields) ->
                /// Names of the struct fields
                let (fieldNames, _) = List.unzip fields
                /// Offset of the selected struct field from the beginning of
                /// the struct
                let offset = List.findIndex (fun f -> f = field) fieldNames
                /// Assembly code that performs the field value assignment
                let assignCode =
                    match rhs.Type with
                    | t when (isSubtypeOf rhs.Env t TUnit) ->
                        Asm() // Nothing to do
                    | t when (isSubtypeOf rhs.Env t TFloat) ->
                        Asm(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(offset * 4),
                                     Reg.r(env.Target)),
                            $"Assigning value to struct field '%s{field}'")
                    | _ ->
                        Asm([(RV.SW(Reg.r(env.Target + 1u), Imm12(offset * 4),
                                    Reg.r(env.Target)),
                              $"Assigning value to struct field '%s{field}'")
                             (RV.MV(Reg.r(env.Target), Reg.r(env.Target + 1u)),
                              "Copying assigned value to target register")])
                // Put everything together
                selTargetCode ++ rhsCode ++ assignCode
            | t ->
                failwith $"BUG: field selection on invalid object type: %O{t}"

        | ArrayElem(target, index) ->
            /// Assembly code for computing the 'target' array object of which we are
            /// retrieving the 'length'.  We write the computation result (which
            /// should be an array memory address) in the target register.
            let arrTargetCode = doCodegen env target
            /// Code for computing the 'index' of the array element to be selected
            let indexCode = doCodegen {env with Target = env.Target + 1u} index
            /// Code for the 'rhs', leaving its result in the target+2 register
            let rhsCode = doCodegen {env with Target = env.Target + 2u} rhs

            let indexOutBoundsCode = checkIndexOutOfBounds env target (index, index) lhs

            match (expandType target.Env target.Type) with
            | TArray _ ->
                /// Offset of the selected index from the beginning of the array container region on heap
                let offsetCode = Asm([
                                     (RV.LW(Reg.r(env.Target), Imm12(4), Reg.r(env.Target)),
                                      "Load the array container pointer from 2nd array instance field (~data)")
                                     (RV.ADDI(Reg.r(env.Target + 2u), Reg.zero, Imm12(4)),
                                      "Load word size for array element offset computation")
                                     (RV.MUL(Reg.r(env.Target + 1u),
                                                      Reg.r(env.Target + 1u),
                                                      Reg.r(env.Target + 2u)),
                                     "Compute offset of the selected array element 4 x index")
                                     (RV.ADD(Reg.r(env.Target),
                                                     Reg.r(env.Target),
                                                     Reg.r(env.Target + 1u)),
                                     "Add offset to the array container address")])
                /// Assembly code that performs the field value assignment
                let assignCode =
                    match rhs.Type with
                    | t when (isSubtypeOf rhs.Env t TUnit) ->
                        Asm() // Nothing to do
                    | t when (isSubtypeOf rhs.Env t TFloat) ->
                        Asm(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(0),
                                     Reg.r(env.Target)),
                            $"Assigning value to array element at index")
                    | _ ->
                        Asm([(RV.SW(Reg.r(env.Target + 2u), Imm12(0),
                                    Reg.r(env.Target)),
                              $"Assigning value to array element at index")
                             (RV.MV(Reg.r(env.Target), Reg.r(env.Target + 2u)),
                              "Copying assigned value to target register")])
                // Put everything together
                indexOutBoundsCode ++ arrTargetCode ++ indexCode ++ offsetCode ++ rhsCode ++ assignCode
            | t ->
                failwith $"BUG: array length retrieved on invalid object type: %O{t}"
        | _ ->
            failwith ($"BUG: assignment to invalid target:%s{Util.nl}"
                      + $"%s{PrettyPrinter.prettyPrint lhs}")

    | While(cond, body) ->
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
        Asm(RV.LABEL(whileBeginLabel))
            ++ (doCodegen env cond)
                .AddText([
                    (RV.BNEZ(Reg.r(env.Target), whileBodyBeginLabel),
                     "Jump to loop body if 'while' condition is true")
                    (RV.LA(Reg.r(env.Target), whileEndLabel),
                     "Load address of label at the end of the 'while' loop")
                    (RV.JR(Reg.r(env.Target)), "Jump to the end of the loop")
                    (RV.LABEL(whileBodyBeginLabel),
                     "Body of the 'while' loop starts here")
                ])
            ++ (doCodegen env body)
            .AddText([
                (RV.LA(Reg.r(env.Target), whileBeginLabel),
                 "Load address of label at the beginning of the 'while' loop")
                (RV.JR(Reg.r(env.Target)), "Jump to the end of the loop")
                (RV.LABEL(whileEndLabel), "")
            ])

    | DoWhile(body, cond) ->
        /// Label to mark the beginning of the 'do-while' loop body
        let doWhileBodyBeginLabel = Util.genSymbol "do_while_body_begin"

        let scopeTarget = env.Target + 1u
        let scopeEnv = { env with Target = scopeTarget}

        Asm(RV.LABEL(doWhileBodyBeginLabel))
            ++ (doCodegen env body)
            ++ (doCodegen scopeEnv cond)
                .AddText([
                    (RV.BNEZ(Reg.r(scopeTarget), doWhileBodyBeginLabel),
                     "Jump to loop body if 'while' condition is true")
                ])

    | Lambda(args, body) ->
        /// Label to mark the position of the lambda term body
        let funLabel = Util.genSymbol "lambda"

        /// Names of the Lambda arguments
        let argNames, _ = List.unzip args

        /// Types of the Lambda arguments - retrieved from the type-checking environment
        let targs = List.map (fun a -> body.Env.Vars[a]) argNames

        /// Perform closure conversion on the lambda term, for immutable variable closures
        let closureConversionCode = closureConversion env funLabel node None args targs body

        closureConversionCode

    | Application(expr, args) ->
        /// Integer registers to be saved on the stack before executing the
        /// function call, and restored when the function returns.  The list of
        /// saved registers excludes the target register for this application.
        /// Note: the definition of 'saveRegs' uses list comprehension:
        /// https://en.wikibooks.org/wiki/F_Sharp_Programming/Lists#Using_List_Comprehensions
        let saveRegs =
            List.except [Reg.r(env.Target)]
                        (Reg.ra :: [for i in 0u..7u do yield Reg.a(i)]
                         @ [for i in 0u..6u do yield Reg.t(i)])
        // Here we also create a list of FP registers to save as per callee and caller convention. For caller we save fa and ft registers. 
        // We use filter and compare for the list because of a small bug/issue with .except that sometimes it wouldn't exclude the target register and hence overwrite it                
        let saveFPRegs = 
            List.filter (fun (e: FPReg) -> e.Number <> env.FPTarget)
                        ([for i in 0u..7u do yield FPReg.fa(i)]
                        @ [for i in 0u..11u do yield FPReg.ft(i)])

        let closurePlainFAccessCode = Asm(RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target)),
                                          "Load plain function address `~f` from closure")

        /// Assembly code for the expression being applied as a function
        let appTermCode =
            Asm().AddText(RV.COMMENT("Load expression to be applied as a function"))
            ++ (doCodegen env expr)
             ++ closurePlainFAccessCode

        /// Indexed list of argument expressions split by type.  We will use the index
        /// as an offset (above the current target register) to determine the target
        /// register for compiling each expression.
        let indexedArgsFloat, indexedArgsInt =
            [expr] @ args
            |> List.partition (fun arg -> isSubtypeOf arg.Env arg.Type TFloat)
            |> fun (floats, ints) -> (List.indexed floats, List.indexed ints)

        /// Function that compiles a float argument (using its index to determine its
        /// target register by type) and accumulates the generated assembly code
        let compileArgFloat (acc: Asm) (i: int, arg: TypedAST) =
            acc ++ (doCodegen {env with FPTarget = env.FPTarget + (uint i)} arg)
        /// Function that compiles an int argument (using its index to determine its
        /// target register by type) and accumulates the generated assembly code
        let compileArgInt (acc: Asm) (i: int, arg: TypedAST) =
            acc ++ (doCodegen {env with Target = env.Target + (uint i) + 1u} arg)

        /// Assembly code of all application arguments, obtained by folding over (int/float)
        let floatArgsCode =
            List.fold compileArgFloat (Asm()) indexedArgsFloat
        let intArgsCode =
            List.fold compileArgInt (Asm()) indexedArgsInt

        /// Function that copies the content of a target register (used by
        /// 'compileArgs' and 'argsCode' above) into an 'a' register, using an
        /// index to determine the source and target registers, and accumulating
        /// the generated assembly code
        let copyArg (acc: Asm) (i: int, arg: TypedAST) (wordOffset: int)=
            let argOffset = (i - 8 + wordOffset) * 4

            match arg.Type with
            | t when (isSubtypeOf arg.Env t TFloat) ->
                // Here we handle float types
                if i < 8 then
                    acc.AddText(RV.FMV_S(FPReg.fa(uint i), FPReg.r(env.FPTarget + (uint i))),
                        $"Load float function call argument %d{i+1} from FP register '%s{FPReg.r(env.FPTarget + (uint i)).ToString()}' to target FP register 'fa%d{i}'") // Better debug comment
                else
                    acc.AddText(RV.FSW_S(FPReg.r(env.FPTarget + (uint i)), Imm12(argOffset), Reg.sp),
                        $"Store float function call argument %d{i+1} to stack at offset {argOffset}")
            | _ ->
                // Here we handle integer types
                if i < 8 then
                    acc.AddText(RV.MV(Reg.a(uint i), Reg.r(env.Target + (uint i) + 1u)),
                                $"Load function call argument %d{i+1}")
                else
                    acc.AddText(RV.SW(Reg.r(env.Target + (uint i) + 1u), Imm12(argOffset), Reg.sp),
                        $"Store function call argument %d{i+1} to stack at offset {argOffset}")

        let floatArgsOnStack = max 0 (indexedArgsFloat.Length - 8)
        let intArgsOnStack = max 0 (indexedArgsInt.Length - 8)

        /// Code that loads each application argument into a register 'a', by
        /// copying the contents of the target registers used by 'compileArgs'
        /// and 'argsCode' above.  To this end, this code folds over the indexes
        /// of all arguments (from 0 to args.Length), using 'copyArg' above.
        let argsLoadCode =
            // Calculate the exact number of arguments that overflow to stack (for stack allocation)
            let stackAdjustment =
                if (floatArgsOnStack + intArgsOnStack) > 0 then
                    Asm(RV.ADDI(Reg.sp, Reg.sp, Imm12(-4 * (floatArgsOnStack + intArgsOnStack))),
                                    $"Update stack pointer for the overflowing args with overflow of %d{floatArgsOnStack + intArgsOnStack} units")
                else
                    Asm()
            let floatArgsLoadCode = List.fold (fun acc arg -> copyArg acc arg 0) (Asm()) indexedArgsFloat
            let intArgsLoadCode = List.fold (fun acc arg -> copyArg acc arg floatArgsOnStack) (Asm()) indexedArgsInt
            stackAdjustment ++ floatArgsLoadCode ++ intArgsLoadCode

        /// Code that performs the function call
        let callCode =
            appTermCode
            //++ argsCode // Code to compute each argument of the function call
            ++ floatArgsCode
            ++ intArgsCode
               .AddText(RV.COMMENT("Before function call: save caller-saved registers"))
               ++ (saveRegisters saveRegs saveFPRegs)
               ++ argsLoadCode // Code to load arg values into arg registers
                  .AddText(RV.JALR(Reg.ra, Imm12(0), Reg.r(env.Target)), "Function call")
        
        /// Code that handles the function return value (if any)
        /// We now check if it is a Function then we check the return type to target the correct output register, FPReg for float, Reg for int.
        let retCode =
            match expr.Type with
            | TFun (_, retType) -> 
                match retType with
                | TFloat ->
                    Asm(RV.FMV_S(FPReg.r(env.FPTarget), FPReg.fa0),
                    $"Copy function return value to target floating point register")
                | _ -> 
                    Asm(RV.MV(Reg.r(env.Target), Reg.a0),
                    $"Copy function return value to target register")
            | _ -> failwith ""
            

        // Put everything together, and restore the caller-saved registers
        callCode
            .AddText(RV.COMMENT("After function call"))
            ++ retCode
            .AddText([
                       (RV.ADDI(Reg.sp, Reg.sp, Imm12(4 * (floatArgsOnStack + intArgsOnStack))),
                        $"Restore SP by {floatArgsOnStack + intArgsOnStack} function args after function call")
                       (RV.COMMENT("Restore caller-saved registers"),"")
                        ])
                  ++ (restoreRegisters saveRegs saveFPRegs)
        
    | StructCons(fields) ->
        // To compile a structure constructor, we allocate heap space for the
        // whole struct instance, and then compile its field initialisations
        // one-by-one, storing each result in the corresponding heap location.
        // The struct heap address will end up in the 'target' register - i.e.
        // the register will contain a pointer to the first element of the
        // allocated structure
        let (fieldNames, fieldInitNodes) = List.unzip fields
        /// Generate the code that initialises a struct field, and accumulates
        /// the result.  This function is folded over all indexed struct fields,
        /// to produce the assembly code that initialises all fields.\
        let folder = fun (acc: Asm) (fieldOffset: int, fieldInit: TypedAST) ->
            /// Code that initialises a single struct field.  Each field init
            /// result is compiled by targeting the register (target+1u),
            /// because the 'target' register holds the base memory address of
            /// the struct.  After the init result for a field is computed, we
            /// copy it into its heap location, by adding the field offset
            /// (multiplied by 4, i.e. the word size) to the base struct address
            let fieldInitCode: Asm =
                match fieldInit.Type with
                | t when (isSubtypeOf fieldInit.Env t TUnit) ->
                    Asm() // Nothing to do
                | t when (isSubtypeOf fieldInit.Env t TFloat) ->
                    Asm(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(fieldOffset * 4),
                                 Reg.r(env.Target)),
                        $"Initialize struct field '%s{fieldNames.[fieldOffset]}'")
                | _ ->
                    Asm(RV.SW(Reg.r(env.Target + 1u), Imm12(fieldOffset * 4),
                              Reg.r(env.Target)),
                        $"Initialize struct field '%s{fieldNames.[fieldOffset]}'")
            acc ++ (doCodegen {env with Target = env.Target + 1u} fieldInit)
                ++ fieldInitCode
        /// Assembly code for initialising each field of the struct, by folding
        /// the 'folder' function above over all indexed struct fields (we use
        /// the index to know the offset of a field from the beginning of the
        /// struct)
        let fieldsInitCode =
            List.fold folder (Asm()) (List.indexed fieldInitNodes)

        /// Assembly code that allocates space on the heap for the new
        /// structure, through an 'Sbrk' system call.  The size of the structure
        /// is computed by multiplying the number of fields by the word size (4)
        let structAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.LI(Reg.a0, fields.Length * 4),
                     "Amount of memory to allocate for a struct (in bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                    (RV.ECALL, "")
                    (RV.MV(Reg.r(env.Target), Reg.a0),
                     "Move syscall result (struct mem address) to target")
                ])
                ++ (afterSysCall [Reg.a0] [])

        // Put everything together: allocate heap space, init all struct fields
        structAllocCode ++ fieldsInitCode

    | FieldSelect(target, field) ->
        // To compile a field selection, we first execute the 'target' object of
        // the field selection, whose code is expected to leave a struct memory
        // address in the environment's 'target' register; then use the 'target'
        // type to determine the memory offset where the selected field is
        // located, and retrieve its value.

        /// Generated code for the target object whose field is being selected
        let selTargetCode = doCodegen env target
        /// Assembly code to access the struct field in memory (depending on the
        /// 'target' type) and leave its value in the target register
        let fieldAccessCode =
            match (expandType node.Env target.Type) with
            | TStruct(fields) ->
                let (fieldNames, fieldTypes) = List.unzip fields
                let offset = List.findIndex (fun f -> f = field) fieldNames
                match fieldTypes.[offset] with
                | t when (isSubtypeOf node.Env t TUnit) ->
                    Asm() // Nothing to do
                | t when (isSubtypeOf node.Env t TFloat) ->
                    Asm(RV.FLW_S(FPReg.r(env.FPTarget), Imm12(offset * 4),
                                 Reg.r(env.Target)),
                        $"Retrieve value of struct field '%s{field}'")
                | _ ->
                    Asm(RV.LW(Reg.r(env.Target), Imm12(offset * 4),
                              Reg.r(env.Target)),
                        $"Retrieve value of struct field '%s{field}'")
            | t ->
                failwith $"BUG: FieldSelect codegen on invalid target type: %O{t}"

        // Put everything together: compile the target, access the field
        selTargetCode ++ fieldAccessCode

    | ArrayCons(length, init) ->
        // To compile an array constructor, we allocate heap space for the whole array
        // instance (struct + container), and then compile its initialisation once and
        // for all elements, storing each result in the corresponding heap location.
        // The struct heap address will end up in the 'target' register - i.e.
        // the register will contain a pointer to the first element of the
        // allocated structure

        /// Register allocations:
        /// env.Target: array object (struct) base address - 2 fields
        /// env.Target + 1u: array length
        /// env.Target + 2u: array sequence base address - array of n elements
        let lengthCode = doCodegen {env with Target = env.Target + 1u} length

        /// Assembly code that allocates space on the heap for the new array sequence,
        /// through a 'Sbrk' system call.  The size of the structure
        /// is computed by multiplying the number of elements by the word size (4)
        let arrayAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.LI(Reg.r(env.Target), 4), "Store word size")
                    (RV.MUL(Reg.a0, Reg.r(env.Target), Reg.r(env.Target + 1u)),
                     "Amount of memory to allocate for the array sequence (in bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                    (RV.ECALL, "")
                    (RV.MV(Reg.r(env.Target + 2u), Reg.a0),
                     "Move syscall result (array mem address) to `target+2`")
                ])
                ++ (afterSysCall [Reg.a0] [])

        /// Allocation of heap space for the new array struct through a 'Sbrk'
        /// system call. The size of the structure is 8 bytes (2 fields x 4 bytes)
        let structAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.ADDI(Reg.a0, Reg.zero, Imm12(8)),
                     "Amount of memory to allocate for array struct (2 fields, in bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                    (RV.ECALL, "")
                    (RV.MV(Reg.r(env.Target), Reg.a0),
                     "Move syscall result (struct mem address) to target")
                ])
                ++ (afterSysCall [Reg.a0] [])

        /// Code to store the length of the array at the beginning of the array struct memory
        let instanceFieldSetCode =
            match length.Type with
            | TInt -> Asm().AddText([
                            (RV.SW(Reg.r(env.Target + 1u), Imm12(0), Reg.r(env.Target)),
                            "Store array length at the beginning of the array memory (1st field)")
                            (RV.SW(Reg.r(env.Target + 2u), Imm12(4), Reg.r(env.Target)),
                            "Store array container pointer in data (2nd struct field)")
                        ])
            | _ -> failwith $"BUG: array length initialised with invalid type: %O{length.Type}"

        /// Compiled code for initialisation value, targeting the register `target+3`
        let initCode = doCodegen {env with Target = env.Target + 3u} init

        /// Assembly code that initialises a single array element by assigning the pre-computed init
        /// value stored in `target+3u` to the heap location of the next array element in `target+2u`
        let elemInitCode: Asm =
            match init.Type with
            | t when (isSubtypeOf init.Env t TUnit) ->
                Asm() // Nothing to do
            | t when (isSubtypeOf init.Env t TFloat) ->
                Asm(RV.FSW_S(FPReg.r(env.FPTarget), Imm12(0), Reg.r(env.Target + 2u)),
                    $"Initialize next array element")
            | _ ->
                Asm(RV.SW(Reg.r(env.Target + 3u), Imm12(0), Reg.r(env.Target + 2u)),
                    $"Initialize next array element")

        /// Assembly code for initialising each element of the array container with pre-computed init,
        /// by looping through the array length and storing the value on heap. The element offset from data
        /// pointer computed in register `target+2` and the element value in register `target+3`.

        /// Label for array loop start
        let loopStartLabel = Util.genSymbol "array_init_loop_start"
        /// Label for array loop end
        let loopEndLabel = Util.genSymbol "array_init_loop_end"

        /// Register allocations:
        /// env.Target: array object base address (computed)
        /// env.Target + 1u: length of array (computed)
        /// env.Target + 2u: array container base address (computed)
        /// env.Target + 2u: memory address of next array element (initially: array container address)
        /// env.Target + 3u: initialisation value (computed)

        /// Use the precomputed length as a downward loop counter
        /// Use the precomputed container memory address as a forward element address iterator
        let initArrayLoopCode =
            Asm().AddText([
                (RV.LABEL(loopStartLabel), "Start of array initialisation loop")
                (RV.BEQZ(Reg.r(env.Target + 1u), loopEndLabel), "Exit loop if remaining length is 0")
            ])
            ++ elemInitCode ++
            Asm().AddText([
                (RV.ADDI(Reg.r(env.Target + 2u), Reg.r(env.Target + 2u), Imm12(4)),
                 "Increment element address by word size")
                (RV.ADDI(Reg.r(env.Target + 1u), Reg.r(env.Target + 1u), Imm12(-1)), "Decrement remaining length")
                (RV.BNEZ(Reg.r(env.Target + 1u), loopStartLabel), "Loop back if remaining length is not 0")
                (RV.LABEL(loopEndLabel), "End of array initialisation loop")
            ])

        // Put everything together: allocate heap space, init all struct fields
        lengthCode ++ arrayAllocCode ++ structAllocCode ++ instanceFieldSetCode ++ initCode ++ initArrayLoopCode

    | ArrayElem(array, index) ->
        /// To compile an array element access operation, we first compile the `array` pointer
        /// referencing the array instance, into the `target` register. Then, we compile the
        /// `index` expression to compute the offset of the element to access, indexed from the
        /// `data` instance field referencing the array container. Finally, we retrieve the
        /// element value from the heap memory address obtained.
        let indexOutBoundsCode = checkIndexOutOfBounds env array (index, index) node

        let arrayTargetCode = doCodegen env array
        let indexCode = doCodegen {env with Target = env.Target + 1u} index

        /// Code to compute the element offset within array container memory
        let memorySetCode = Asm().AddText([
            // Register env.Target: array instance reference [length; data] -> array container pointer
            // The data pointer (field) in the array instance can be loaded from `target` with offset 4 (2nd field)
            (RV.LW(Reg.r(env.Target), Imm12(4), Reg.r(env.Target)),
             "Load the container base address into target register from instance data pointer")
            (RV.LI(Reg.r(env.Target + 2u), 4),
             "Load word size for array element offset computation")
            (RV.MUL(Reg.r(env.Target + 1u), Reg.r(env.Target + 1u), Reg.r(env.Target + 2u)),
             "Compute offset of the selected array element as 4 x index")
            (RV.ADD(Reg.r(env.Target + 1u), Reg.r(env.Target), Reg.r(env.Target + 1u)),
             "Memory address of the selected array element (container pointer + offset)")
        ])

        /// Code that accesses a single array element. The `target` register holds
        /// the base memory address of the array. The `target+1` register holds the
        /// current element address in memory. We load the element value from the
        /// heap location, with 0 offset from the computed element address.
        let elemAccessCode: Asm =
            match array.Type, index.Type with
            | TArray elemType, TInt ->
                match elemType with
                | t when (isSubtypeOf array.Env t TUnit) ->
                    Asm() // Nothing to do
                | t when (isSubtypeOf array.Env t TFloat) ->
                    Asm(RV.FLW_S(FPReg.r(env.FPTarget), Imm12(0),
                                 Reg.r(env.Target + 1u)),
                        $"Access array element")
                | _ ->
                    Asm(RV.LW(Reg.r(env.Target), Imm12(0),
                              Reg.r(env.Target + 1u)),
                        $"Access array element")
            | TArray _, _ -> failwith $"BUG: array element access with invalid index type: %O{index.Type}"
            | _, TInt
            | _ -> failwith $"BUG: element access on invalid target: %O{array.Type}"

        indexOutBoundsCode ++ arrayTargetCode ++ indexCode ++ memorySetCode ++ elemAccessCode

    | ArrayLength(target) ->
        /// To compile an array length operation, we first compile the array `target` pointer
        /// referencing the array into the `target` register. Then, we access the
        /// heap memory at `target` (the beginning of the array) to retrieve the length value.
        let targetCode = doCodegen env target
        let lengthAccessCode =
            match target.Type with
            | TArray _ ->
                Asm().AddText(
                    RV.LW(Reg.r(env.Target), Imm12(0), Reg.r(env.Target)),
                    "Load array length from base pointer in memory"
                )
            | _ -> failwith $"BUG: array length access on invalid target: %O{target.Type}"
        targetCode ++ lengthAccessCode

    | ArraySlice(parent, startIdx, endIdx) ->
        // To compile an array slice definition, we allocate heap space for an array instance
        // without a new container, hence only a struct with 2 fields: `length` and `data`.
        // The struct heap address will end up in the 'target' register. The `data` field
        // contains a pointer to the memory address of the first slice element from the container.

        let indexOutBoundsCode = checkIndexOutOfBounds env parent (startIdx, endIdx) node

        /// Compile the parent array as target
        let parentCode = doCodegen env parent

        /// Compile the start index of the slice
        let startIndexCode = doCodegen { env with Target = env.Target + 2u } startIdx

        /// Assembly code to compute the updated data pointer of the slice based on start offset
        let dataPointerCode =
            match parent.Type, startIdx.Type with
            | TArray _, TInt ->
                Asm().AddText([
                    (RV.LW(Reg.r(env.Target + 1u), Imm12(4), Reg.r(env.Target)),
                     "Load the parent array data pointer in register `target+1`")
                    (RV.LI(Reg.r(env.Target + 3u), 4),
                     "Store word size in register for word-aligned slice start computation")
                    (RV.MUL(Reg.r(env.Target + 2u), Reg.r(env.Target + 2u), Reg.r(env.Target + 3u)),
                     "Multiply the slice start offset by 4 for word-alignment ( 4 x startIdx )")
                    (RV.ADD(Reg.r(env.Target + 1u), Reg.r(env.Target + 1u), Reg.r(env.Target + 2u)),
                     "Update data pointer from parent array with start index offset")
                ])
            | TArray _, _ -> failwith $"BUG: slice with invalid index type: %O{startIdx.Type}"
            | _, TInt
            | _ -> failwith $"BUG: slice on invalid array target: %O{parent.Type}"

        /// Allocation of heap space for the new array struct through a 'Sbrk'
        /// system call. The size of the structure is 8 bytes (2 fields x 4 bytes)
        let structAllocCode =
            (beforeSysCall [Reg.a0] [])
                .AddText([
                    (RV.ADDI(Reg.a0, Reg.zero, Imm12(8)),
                     "Amount of memory to allocate for array struct (2 fields, in bytes)")
                    (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                    (RV.ECALL, "")
                    (RV.MV(Reg.r(env.Target), Reg.a0),
                     "Move syscall result (struct mem address) to target")
                ])
                ++ (afterSysCall [Reg.a0] [])

        /// Construct typed AST node for the resulting array slice length
        let lengthNode = { node with Expr = Add({ node with Expr = Sub(endIdx, startIdx)
                                                            Type = TInt },
                                                { node with Expr = IntVal(1)
                                                            Type = TInt })
                                     Type = TInt }

        /// Compile the array slice length in register `target+2`
        let lengthCode = doCodegen { env with Target = env.Target + 2u } lengthNode

        /// Code to store the length of the array at the beginning of the array struct memory
        let instanceFieldSetCode =
                Asm().AddText([
                    (RV.SW(Reg.r(env.Target + 2u), Imm12(0), Reg.r(env.Target)),
                    "Store array length at the beginning of the array memory (1st field)")
                    (RV.SW(Reg.r(env.Target + 1u), Imm12(4), Reg.r(env.Target)),
                    "Store array container pointer in data (2nd struct field)")
                ])

        indexOutBoundsCode
            ++ parentCode ++ startIndexCode ++ dataPointerCode
            ++ structAllocCode ++ lengthCode ++ instanceFieldSetCode

    | Pointer(_) ->
        failwith "BUG: pointers cannot be compiled (by design!)"

    | Copy(arg) ->
        match arg.Type with
        | TStruct(fields) ->

            // Define registers used by this level of copy
            let outerDestReg = Reg.r(env.Target)      // Holds new struct address
            let outerSourceReg = Reg.r(env.Target + 1u) // Holds original struct address
            let tempReg = Reg.r(env.Target + 2u) // Temporarily holds the results of copy
            let fpTempReg = FPReg.r(env.FPTarget) // Floating Point register for copying floats

            // Generate the code for the target struct
            // Place the result (original address) into outerSourceReg
            let targetCode = doCodegen { env with Target = env.Target + 1u } arg

            // Allocate heap space for the new struct
            // Place result (new address) into outerDestReg
            let structAllocCode =
                (beforeSysCall [ Reg.a0 ] []) // Syscall clobbers a0, a7
                    .AddText(
                        [ (RV.LI(Reg.a0, (fields.Length * 4)), "Amount of memory to allocate for a struct (in bytes)")
                          (RV.LI(Reg.a7, 9), "RARS syscall: Sbrk")
                          (RV.ECALL, "")
                          (RV.MV(outerDestReg, Reg.a0), "Move syscall result (new struct mem address) to outer Dest register") ]
                    )
                ++ (afterSysCall [ Reg.a0 ] []) // Restore registers potentially clobbered by syscall


            // Folder function that generates the code for copying a struct field
            let folder =
                fun (acc: Asm) (fieldOffset: int, (fName, fType)) ->
                    let fieldMemOffset = Imm12(fieldOffset * 4)
                    let fieldCommentName = $"field '{fName}'"

                    let fieldCopyCode: Asm =
                        match expandType node.Env fType with
                        | TStruct(fields') ->
                            //Recursively copy the struct field by reusing registers, saving context in the stack
                            
                            let stackSpace = 8 // Space for 2 registers (4 bytes each)

                            // 1. Save outer context
                            let saveContextCode =
                                Asm().AddText([
                                    (RV.ADDI(Reg.sp, Reg.sp, Imm12(-stackSpace)), "Make stack space to save registers")
                                    (RV.SW(outerSourceReg, Imm12(0), Reg.sp),    "Save outer source addr")
                                    (RV.SW(outerDestReg, Imm12(4), Reg.sp),      "Save outer dest addr")
                                ])

                            // 2. Recursively copy struct reusing registers
                            let recursiveCopyCode =
                                doCodegen
                                     env // Do not recursively increment registers to avoid running out of registers
                                    { node with
                                        Expr =
                                            Copy( 
                                                { node with
                                                    Expr = FieldSelect(arg, fName)
                                                    Type = fType }
                                            )
                                        Type = fType }

                            // 3. Move the result to tempReg before restoring context
                            let moveResultToTempCode =
                                Asm().AddText([
                                    (RV.MV(tempReg, outerDestReg), "Move nested copy result to tempReg")
                                ])

                            // 4. Restore outer context from the stack
                            let restoreContextCode =
                                Asm().AddText([
                                    (RV.LW(outerSourceReg, Imm12(0), Reg.sp),    "Restore outer source addr")
                                    (RV.LW(outerDestReg, Imm12(4), Reg.sp),      "Restore outer dest addr")
                                    (RV.ADDI(Reg.sp, Reg.sp, Imm12(stackSpace)), "Release stack space")
                                ])

                            // 5. Store the nested struct pointer into the appropriate field
                            let storeResultCode =
                                Asm().AddText([
                                    (RV.SW(tempReg, fieldMemOffset, outerDestReg),
                                     $"Store recursively copied {fieldCommentName} addr into outer dest")
                                ])

                            // Combine the steps for the recursive case
                            saveContextCode ++ recursiveCopyCode ++ moveResultToTempCode  ++ restoreContextCode ++ storeResultCode

                        | TFloat ->
                            // For float fields, use floating-point registers
                            Asm(
                                [ (RV.FLW_S(fpTempReg, fieldMemOffset, outerSourceReg),
                                   $"Load float {fieldCommentName} from source")
                                  (RV.FSW_S(fpTempReg, fieldMemOffset, outerDestReg),
                                   $"Store float {fieldCommentName} to dest") ]
                            )
                        | _ ->
                            // For other field types (int, bool), use standard registers
                            Asm(
                                [ (RV.LW(tempReg, fieldMemOffset, outerSourceReg),
                                   $"Load field {fieldCommentName} from source")
                                  (RV.SW(tempReg, fieldMemOffset, outerDestReg),
                                   $"Store field {fieldCommentName} to dest") ]
                            )

                    acc ++ fieldCopyCode // Accumulate code for this field

            // Generate the code for copying all the fields using the folder function
            let copyCode =
                 fields
                 |> List.mapi (fun i (fName, fType) -> (i, (fName, fType))) // Add index as offset
                 |> List.fold folder (Asm()) // Apply folder to generate copy code for all fields

            
            targetCode ++ structAllocCode ++ copyCode

        | _ -> failwith "BUG: Copy expression on non-struct"
             
        

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

/// Compile a function instance with the given (optional) name, arguments, and
/// body, and using the given environment.  This function places all the
/// assembly code it generates in the Text segment (hence, this code may need
/// to be moved afterwards).
and internal compileFunction (args: List<string * Type>)
                             (body: TypedAST)
                             (env: CodegenEnv): Asm =
    /// Indexed lists of argument expressions split by type. We will use the index as the number
    /// of the 'a' register that holds the argument, with respect to its own type.
    let indexedArgsFloat, indexedArgsInt =
        args
        |> List.partition (fun (_, tpe) -> isSubtypeOf body.Env tpe TFloat)
        |> fun (floats, ints) -> (List.indexed floats, List.indexed ints)

    let floatArgsCount = indexedArgsFloat.Length
    let intArgsCount = indexedArgsInt.Length

    /// Folder function that assigns storage information to function arguments:
    /// it assigns an 'a' register to each function argument, and accumulates
    /// the result in a mapping (that will be used as env.VarStorage)
    let folder (acc: Map<string, Storage>) (i, (var, _tpe)) =
        match _tpe with
        | t when (isSubtypeOf body.Env t TFloat) ->
            if i < 8 then
                acc.Add(var, Storage.FPReg(FPReg.fa(uint i)))
            else
                // Args beyond our 8 registers are at a (+) offset from frame pointer
                let offset = (i - 8) * 4
                acc.Add(var, Storage.Frame offset)
        | _ ->
        // Handle all else since everything else is an int.+
            if i < 8 then
                acc.Add(var, Storage.Reg(Reg.a((uint)i)))
            else
                // Account for float args already on the stack...as ints are handled second by the caller
                let floatArgsOnStack = max 0 (floatArgsCount - 8)
                // Args beyond our 8 registers are at a (+) offset from frame pointer
                let offset = (i - 8 + floatArgsOnStack) * 4
                acc.Add(var, Storage.Frame offset)

    /// Updated storage information including function arguments
    let varStorage2 = List.fold folder env.VarStorage (indexedArgsFloat @ indexedArgsInt)

    /// Code for the body of the function, using the newly-created
    /// variable storage mapping 'varStorage2'.  NOTE: the function body
    /// compilation restarts the target register numbers from 0.  Consequently,
    /// the function body result (i.e. the function return value) will be stored
    /// in Reg.r(0) or FPReg.r(0) (depending on its type); when the function
    /// ends, we need to move that result into the function return value
    /// register 'a0' or 'fa0'.
    let bodyCode =
        let env = {Target = 0u; FPTarget = 0u; VarStorage = varStorage2; TopLevel = false}
        doCodegen env body

    /// Code to move the body result into the function return value register
    let returnCode =
        match body.Type with
        | t when (isSubtypeOf body.Env t TFloat) ->
            Asm(RV.FMV_S(FPReg.fa0, FPReg.r(0u)),
                "Move float result of function into return value register")
        | _ ->
            Asm(RV.MV(Reg.a0, Reg.r(0u)),
                "Move result of function into return value register")

    /// Integer registers to save before executing the function body.
    /// Note: the definition of 'saveRegs' uses list comprehension:
    /// https://en.wikibooks.org/wiki/F_Sharp_Programming/Lists#Using_List_Comprehensions
    let saveRegs = [for i in 0u..11u do yield Reg.s(i)]
    let saveFPRegs = [for i in 0u..11u do yield FPReg.fs(i)] // Here in callee as per the RISCV guidelines we want to also save/track 'fs' registers.

    // Finally, we put together the full code for the function
    Asm(RV.COMMENT("Function prologue begins here"))
            .AddText(RV.COMMENT("Save callee-saved registers"))
        ++ (saveRegisters saveRegs saveFPRegs)
            .AddText(RV.ADDI(Reg.fp, Reg.sp, Imm12((saveRegs.Length + saveFPRegs.Length) * 4)),
                     "Update frame pointer for the current function")
            .AddText(RV.COMMENT("End of function prologue.  Function body begins"))
        ++ bodyCode
            .AddText(RV.COMMENT("End of function body.  Function epilogue begins"))
        ++ returnCode
            .AddText(RV.COMMENT("Restore callee-saved registers"))
            ++ (restoreRegisters saveRegs saveFPRegs)
                .AddText(RV.JR(Reg.ra), "End of function, return to caller")

and internal closureConversion (env: CodegenEnv) (funLabel: string)
                (node: TypedAST) (name: Option<string>)
                args (targs: Type list) (body: Node<TypingEnv, Type>) =
    let closureEnvVar = "~clos"
    //-----------------------------------Step1: Closure environment type `T_clos`----------------------------------
    /// Save all variables captured by the lambda term, excluding the top-level variables stored at data labels.
    let topLevelFilter = fun (v: string) ->
        match env.VarStorage.TryFind v with
        | Some(Storage.Label _) -> false
        | _ -> true
    let filteredCv = ASTUtil.capturedVars node |> Set.filter topLevelFilter
    /// Remove the env struct - the closure environment is not captured
    let cv = Set.toList (Set.difference filteredCv (Set.singleton closureEnvVar))
    let cvFields = cv |> List.map (fun v -> (v, body.Env.Vars[v]))

    /// Outer closure environment fields - ~clos is safely assumed to be the outer closure environment
    /// Select fields of the outer closure environment - without shadowed captured fields and outer ~f
    let outerClosureFields =
        let outerFields =
            match node.Env.Vars.TryFind closureEnvVar with
            | Some closureType ->
                    match closureType with
                    | TStruct fields -> fields
                    | tpe -> failwith $"Bug: Unknown non-structured closure: {tpe}"
            | None -> []
        List.filter (fun (v, _) -> not ((List.contains v cv) || v = "~f")) outerFields

    /// Define the closure environment type T_clos as a struct with a plain function pointer @f +
    /// outer closure env fields + named fields for each captured variable in the current closure
    let closureEnvType = TStruct([("~f", node.Type)] @ (outerClosureFields @ cvFields))

    //--------------------------Step2: Plain (non-capturing) Function `v'` from Lambda Term-------------------------
    let argNames, _ = List.unzip args // lambda argument names
    let argNamesTypes = List.zip argNames targs // mapping from argument names to their type from TypingEnv
    let closureArgNamesTypes = (closureEnvVar, closureEnvType) :: argNamesTypes

    /// Compute "plain" function by substituting captures with field selections on the environment argument (folding)
    let nonCaptureFolder (fbody: TypedAST) (capturedVar: string) =
        let fieldSelect = FieldSelect({node with Expr = Var(closureEnvVar); Type = closureEnvType}, capturedVar)
        ASTUtil.subst fbody capturedVar {node with Expr = fieldSelect; Type = body.Env.Vars[capturedVar]}
    /// Compute the plain function body by folding over the captured variables (add the closure environment var)
    let plainBody = List.fold nonCaptureFolder (addVarNode body closureEnvVar closureEnvType) cv

    let plainType = TFun(closureEnvType::List.map snd argNamesTypes, node.Type)

    /// Compiled code for the plain function or lambda body, potentially recursive
    let plainBodyCode =
        match node.Expr, name with
        | LetRec _, Some(name) ->
            let recEnv = { env with VarStorage = env.VarStorage.Add(name, Storage.Reg(Reg.a0)) }
            let replacer = {node with Expr = FieldSelect({node with Expr = Var(name); Type = closureEnvType}, "~f"); Type = plainType }
            let recPlainBody = ASTUtil.subst plainBody name replacer
            compileFunction closureArgNamesTypes recPlainBody recEnv
        | _ -> compileFunction closureArgNamesTypes plainBody env

    /// Compiled function code where the function label is located just
    /// before the 'bodyCode', and everything is placed at the end of the
    /// text segment (i.e. in the "PostText")
    let plainFunctionCode =
        (Asm(RV.LABEL(funLabel), "Plain lambda term (fun instance) or named function code")
            ++ plainBodyCode).TextToPostText // Move to the end of text segment


    // Finally, load the plain function address (label) in the target register as storage for v'
    let storeFunctionCode = Asm(RV.LA(Reg.r(env.Target), funLabel),
                                $"Load plain {funLabel} function address")
    let env' = {env with VarStorage = env.VarStorage.Add("~v'", Storage.Reg(Reg.r(env.Target)))
                         Target = env.Target + 1u }

    //----------------------------------Step3: Closure Environment Structure `clos`---------------------------------
    /// Mapper function for pairing environment fields from the surrounding (outer) closure with their values/types
    let outerClosureEnvMapping (name: string, fieldType: Type) =
        /// ~clos is safely assumed to be the outer closure environment - its type can be retrieved
        let closureType = node.Env.Vars[closureEnvVar]
        let closureFieldSelect = FieldSelect({node with Expr = Var(closureEnvVar); Type = closureType}, name)
        (name, {node with Expr = closureFieldSelect; Type = fieldType})

    /// Mapper function for pairing the captured variable name with its value and environment type
    let capturedEnvMapping (name: string, varType: Type) =
        (name, {node with Expr = Var(name); Type = varType})

    /// Construct the list of closure environment fields covering captured variables
    let closureEnvNamedFields =
        (outerClosureFields |> List.map outerClosureEnvMapping) @
        (cvFields |> List.map capturedEnvMapping)
    let clos = { node with
                    Expr = StructCons([("~f", {node with Expr = Var("~v'")
                                                         Type = plainType})]
                                      @ closureEnvNamedFields)
                    Type = closureEnvType }

    /// Compile `clos` into env.Target
    let closCode = doCodegen env' clos

    /// Move closure result pointer into the current env.Target to be returned from compilation
    let moveClosResult = Asm(RV.MV(Reg.r(env.Target), Reg.r(env.Target + 1u)),
                             "Move closure result to target register")

    storeFunctionCode ++ closCode ++ moveClosResult ++ plainFunctionCode

and internal errorSegFaultNode (index: Node<TypingEnv, Type>) (node: Node<TypingEnv, Type>) =
    let error = { node with
                    Expr = Seq([
                        {node with Expr = Print({node with
                                                    Expr = StringVal($"SEGFAULT [{index.Pos.FileName}:{index.Pos.LineStart}:{index.Pos.ColStart}]: Array index out of bounds with value: ")
                                                    Type = TString
                                                })
                                   Type = TUnit}
                        {node with Expr = PrintLn(index)
                                   Type = TUnit}
                        {node with Expr = Assertion({node with Expr = BoolVal(false)
                                                               Type = TBool})
                                   Type = TUnit
                                   Pos = node.Pos }
                    ])
                    Type = TUnit
                    Pos = node.Pos
                }
    error
and internal errorInvalidSlice (indexL: Node<TypingEnv, Type>, indexR: Node<TypingEnv, Type>) (node:Node<TypingEnv, Type>) =
    let error = { node with
                    Expr = Seq([
                        {node with Expr = Print({node with
                                                    Expr = StringVal($"Invalid Slice: [{indexL.Pos.FileName}:{indexL.Pos.LineStart}:{indexL.Pos.ColStart}]: Start index is higher than end index of slice: ")
                                                    Type = TString
                                                })
                                   Type = TUnit}
                        {node with Expr = PrintLn(indexL)
                                   Type = TUnit}
                        {node with Expr = PrintLn(indexR)
                                   Type = TUnit}
                        {node with Expr = Assertion({node with Expr = BoolVal(false)
                                                               Type = TBool})
                                   Type = TUnit
                                   Pos = node.Pos }
                    ])
                    Type = TUnit
                    Pos = node.Pos
                }
    error
and internal checkIndexOutOfBounds env target (indexL, indexR) node: Asm =

    // Create a node to check if index is greater than or equal to 0
    let indexNonNegativeCheck = GreaterEq(indexL, {node with Expr = IntVal(0)})

    // Create a node to check if index is less than array length
    let indexLessThanLengthCheck = Less(indexR, {node with Expr = ArrayLength(target)})

    // Create a node to check if left index is less or equal than right index
    let leftIndexLessEqRightIndexCheck = LessEq(indexL, indexR)

    let sliceNode = match indexL = indexR with
                    | true -> { node with Expr = UnitVal
                                          Type = TUnit }
                    | false -> { node with Expr = If({ node with Expr = leftIndexLessEqRightIndexCheck
                                                                 Type = TBool
                                                                 Pos = node.Pos },
                                                     { node with Expr = UnitVal
                                                                 Type = TUnit },
                                                     errorInvalidSlice (indexL, indexR) node)}

    let indexOutOfBoundsCheck =
            { node with
                Expr = If({ node with Expr = indexNonNegativeCheck
                                      Type = TBool
                                      Pos = node.Pos },
                          { node with Expr = If({ node with Expr = indexLessThanLengthCheck
                                                            Type = TBool
                                                            Pos = node.Pos },
                                                sliceNode,
                                                errorSegFaultNode indexR node)
                                      Type = TUnit },
                          errorSegFaultNode indexL node)
                Type = TUnit
                Pos = node.Pos
            }

    Asm().AddText((RV.COMMENT "Check: Array index out of bounds?")) ++
                                doCodegen env indexOutOfBoundsCheck

/// Generate RISC-V assembly for the given AST.
let codegen (node: TypedAST): RISCV.Asm =
    /// Initial codegen environment, targeting generic registers 0 and without
    /// any variable in the storage map
    let env = {Target = 0u; FPTarget = 0u; VarStorage =  Map[]; TopLevel = true}
    Asm(RV.MV(Reg.fp, Reg.sp), "Initialize frame pointer")
    ++ (doCodegen env node)
        .AddText([
            (RV.LI(Reg.a7, 10), "RARS syscall: Exit")
            (RV.ECALL, "Successful exit with code 0")
        ])
