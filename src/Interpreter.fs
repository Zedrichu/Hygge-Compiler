// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Interpreter for Hygge programs.
module Interpreter

open AST
open System


/// Does the given AST node represent a value?
let rec isValue (node: Node<'E,'T>): bool =
    match node.Expr with
    | UnitVal
    | BoolVal _
    | IntVal _
    | FloatVal _
    | StringVal _ -> true
    | Lambda(_, _) -> true
    | Pointer _ -> true
    | _ -> false


/// Specialized pretty-printer function that returns a very compact, one-line
/// representation of the given AST node, which must be a value (therefore, this
/// function must cover all cases where the function 'isValue' returns 'true').
let prettyPrintValue (node: Node<'E,'T>): string =
    match node.Expr with
    | UnitVal -> "UnitVal ()"
    | IntVal(value) -> $"IntVal %d{value}"
    | BoolVal(value) -> $"BoolVal %b{value}"
    | FloatVal(value) -> $"FloatVal %f{value}"
    | StringVal(value) -> $"StringVal \"%s{value}\""
    | Lambda(args, _) -> $"Lambda (taking %d{args.Length} arguments)"
    | Pointer(addr) -> $"Pointer 0x%x{addr}"
    | _ -> failwith $"BUG: 'prettyPrintValue' called with invalid argument ${node}"


/// Type for the runtime heap: a map from memory addresses to values.  The type
/// parameters have the same meaning of the corresponding ones in
/// AST.Node<'E,'T>: they allow the heap to hold generic instances of
/// AST.Node<'E,'T>.
type internal Heap<'E,'T> = Map<uint, Node<'E,'T>>


/// Runtime environment for the interpreter.  The type parameters have the same
/// meaning of the corresponding ones in AST.Node<'E,'T>: they allow the
/// environment to hold generic instances of AST.Node<'E,'T>.
type internal RuntimeEnv<'E,'T> = {
    /// Function called to read a line when evaluating 'ReadInt' and 'ReadFloat'
    /// AST nodes.
    Reader: Option<unit -> string>
    /// Function called to produce an output when evaluating 'Print' and
    /// 'PrintLn' AST nodes.
    Printer: Option<string -> unit>
    /// Mutable local variables: mapping from their name to their current value.
    Mutables: Map<string, Node<'E,'T>>
    /// Runtime heap, mapping memory addresses to values.
    Heap: Heap<'E,'T>
    /// Pointer information, mapping memory addresses to lists of structure
    /// fields.
    PtrInfo: Map<uint, List<string>>
} with override this.ToString(): string =
        let folder str addr v = str + $"      0x%x{addr}: %s{prettyPrintValue v}%s{Util.nl}"
        let heapStr = if this.Heap.IsEmpty then "{}"
                      else "{" + Util.nl + (Map.fold folder "" this.Heap) + "    }"
        let printFields fields = List.reduce (fun x y -> x + ", " + y) fields
        let folder str addr fields = str + $"      0x%x{addr}: [%s{printFields fields}]%s{Util.nl}"
        let ptrInfoStr = if this.PtrInfo.IsEmpty then "{}"
                         else "{" + Util.nl + (Map.fold folder "" this.PtrInfo) + "    }"
        $"  - Reader: %O{this.Reader}"
          + $"%s{Util.nl}  - Printer: %O{this.Printer}"
          + $"%s{Util.nl}  - Mutables: %s{Util.formatMap this.Mutables}"
          + $"%s{Util.nl}  - Heap: %s{heapStr}"
          + $"%s{Util.nl}  - PtrInfo: %s{ptrInfoStr}"


/// Attempt to reduce the given AST node by one step, using the given runtime
/// environment.  If a reduction is possible, return the reduced node and an
/// updated runtime environment; otherwise, return None.
let rec internal reduce (env: RuntimeEnv<'E,'T>)
                        (node: Node<'E,'T>): Option<RuntimeEnv<'E,'T> * Node<'E,'T>> =
    match node.Expr with
    | UnitVal
    | BoolVal _
    | IntVal _
    | FloatVal _
    | StringVal _ -> None

    | Var(name) when env.Mutables.ContainsKey(name) ->
        Some(env, env.Mutables[name])
    | Var _ -> None

    | Lambda(_, _) -> None

    | Pointer _ -> None

    | Mult(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = IntVal(v1 * v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = FloatVal(v1 * v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Mult(lhs', rhs')})
            | None -> None

    | Add(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = IntVal(v1 + v2)})
        | FloatVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = FloatVal(v1 + single v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = FloatVal(v1 + v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Add(lhs', rhs')})
            | None -> None

    | Sub(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = IntVal(v1 - v2)})
        | FloatVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = FloatVal(v1 - single v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = FloatVal(v1 - v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Sub(lhs', rhs')})
            | None -> None

    | Div(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) when v2 <> 0 ->
            Some(env, {node with Expr = IntVal(v1 / v2)})
        | FloatVal(v1), FloatVal(v2) when v2 <> 0f ->
            Some(env, {node with Expr = FloatVal(v1 / v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Div(lhs', rhs')})
            | None -> None

    | Mod(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) when v2 <> 0 ->
            Some(env, {node with Expr = IntVal(v1 % v2)})
        | _,_ ->
            match(reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Mod(lhs', rhs')})
            | None -> None

    | Sqrt(arg) ->
        match arg.Expr with
        | IntVal(value) when value >= 0 ->
            let sqrt = Math.Sqrt(float value)
            Some(env, {node with Expr = FloatVal(float32 sqrt)})
        | FloatVal(value) when value >= 0.0f ->
            let sqrt = Math.Sqrt(float value)
            Some(env, {node with Expr = FloatVal(float32 sqrt)})
        | _ ->
            match (reduce env arg) with
            | Some(env', arg2) ->
                Some(env', {node with Expr = Sqrt(arg2)})
            | None -> None

    | Min(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = IntVal(min v1 v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = FloatVal(min v1 v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Min(lhs', rhs')})
            | None -> None

    | Max(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = IntVal(max v1 v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = FloatVal(max v1 v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Max(lhs', rhs')})
            | None -> None

    | And(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | BoolVal(v1), BoolVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 && v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = And(lhs', rhs')})
            | None -> None

    | Or(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | BoolVal(v1), BoolVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 || v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Or(lhs', rhs')})
            | None -> None

    | Not(arg) ->
        match arg.Expr with
        | BoolVal(v) ->
            Some(env, {node with Expr = BoolVal(not v)})
        | _ ->
            match (reduce env arg) with
            | Some(env', arg2) ->
                Some(env', {node with Expr = Not(arg2)})
            | None -> None

    | Eq(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 = v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 = v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Eq(lhs', rhs')})
            | None -> None

    | Less(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 < v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 < v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Less(lhs', rhs')})
            | None -> None

    | LessEq(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 <= v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 <= v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = LessEq(lhs', rhs')})
            | None -> None

    | Greater(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 > v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 > v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = Greater(lhs', rhs')})
            | None -> None

    | GreaterEq(lhs, rhs) ->
        match (lhs.Expr, rhs.Expr) with
        | IntVal(v1), IntVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 >= v2)})
        | FloatVal(v1), FloatVal(v2) ->
            Some(env, {node with Expr = BoolVal(v1 >= v2)})
        | _, _ ->
            match (reduceLhsRhs env lhs rhs) with
            | Some(env', lhs', rhs') ->
                Some(env', {node with Expr = GreaterEq(lhs', rhs')})
            | None -> None

    | ReadInt ->
        match env.Reader with
        | None -> None
        | Some(reader) ->
            /// Input read from the runtime environment
            let input = reader()
            // Use the invariant culture to parse the integer value
            match System.Int32.TryParse(input, System.Globalization.NumberStyles.AllowLeadingSign,
                                        System.Globalization.CultureInfo.InvariantCulture) with
            | true, result ->
                Some(env, {node with Expr = IntVal(result)})
            | false, _ ->
                Some(env, {node with Expr = UnitVal})

    | ReadFloat ->
        match env.Reader with
        | None -> None
        | Some(reader) ->
            /// Input read from the console
            let input = reader()
            /// Format used to parse the input
            let format = System.Globalization.NumberStyles.AllowLeadingSign
                         ||| System.Globalization.NumberStyles.AllowDecimalPoint
            // Use the invariant culture to parse the floating point value
            match System.Single.TryParse(input, format,
                                         System.Globalization.CultureInfo.InvariantCulture) with
            | true, result ->
                Some(env, {node with Expr = FloatVal(result)})
            | false, _ ->
                Some(env, {node with Expr = UnitVal})

    | Print(arg) ->
        let rec reduceFullyWithEnv (env: RuntimeEnv<'E,'T>) (node: Node<'E,'T>): RuntimeEnv<'E,'T>*Node<'E,'T> =
            match (reduce env node) with
            | Some(env', node') -> reduceFullyWithEnv env' node'
            | None -> (env, node)
        match env.Printer with
        | None -> None
        | Some(printer) -> // Reductum when printing succeeds (a unit value)
            let reductum = Some(env, {node with Expr = UnitVal})
            match arg.Expr with
            | BoolVal(v) -> printer $"%A{v}"; reductum
            | IntVal(v) -> printer $"%d{v}"; reductum
            | FloatVal(v) -> printer $"%f{v}"; reductum
            | StringVal(v) -> printer $"%s{v}"; reductum
            | Lambda(args,_) -> 
                let argsStr = String.concat ", " (List.map (fun (argName, _) -> $"%s{argName}") args)
                printer $"Lambda({argsStr})"; reductum
            | Pointer(addr) ->
                match (env.PtrInfo.TryFind addr) with
                | Some(fields) ->
                    let nodes = 
                        match fields with
                        | ["~length"; "~data"] ->
                            // Special case for arrays [print as 'Array{ length: 10 }']
                            [{ node with Expr = Print({ node with Expr = StringVal("Array{ length: ") }) }] @
                            [{ node with Expr = Print({ node with Expr = FieldSelect({ node with Expr = Pointer(addr) }, "~length") }) }] @
                            [{ node with Expr = Print({ node with Expr = StringVal(" }") }) }]
                        | _ ->
                            [{ node with Expr = Print({ node with Expr = StringVal("struct { ") }) }] @
                            (List.mapi (fun i field ->
                                // Add quotes around string values
                                let strVals = 
                                    match (env.Heap.TryFind (addr + (uint i))) with
                                    | Some(fieldNode) when (match fieldNode.Expr with StringVal _ -> true | _ -> false) ->
                                        $"{field} = \"", "\"; "
                                    | _ ->
                                        $"{field} = ", "; "
                                [
                                    { node with Expr = Print({ node with Expr = StringVal(fst strVals) }) }
                                    { node with Expr = Print({ node with Expr = FieldSelect({ node with Expr = Pointer(addr) }, field) }) }
                                    { node with Expr = Print({ node with Expr = StringVal(snd strVals) }) }
                                ]
                                ) fields |> List.concat) @
                            [{ node with Expr = Print({ node with Expr = StringVal(" }") }) }]

                    // since this is just Print concatenation, we reduce it fully
                    // such that externally it looks like a single Print and no other modification is needed
                    Some (reduceFullyWithEnv env { node with Expr = Seq(nodes) })
                | None ->
                    // with current implementation, this could be a Union
                    match (env.Heap.TryFind addr) with
                    | Some({Expr = StringVal(label)}) ->
                        // Retrieve the value of the union instance from the heap
                        match (env.Heap.TryFind (addr + 1u)) with
                        | Some(v) ->
                            Some (reduceFullyWithEnv env { node with Expr = Print({ node with Expr = StringVal(label + "{...}")})})
                        | None -> None
                    | _ -> None
            | _ when not (isValue node) ->
                match (reduce env arg) with
                | Some(env', arg2) ->
                    Some(env', {node with Expr = Print(arg2)})
                | None -> None
            | _ -> None

    | PrintLn(arg) ->
        // We recycle the evaluation of 'Print', by rewriting this AST node
        match (reduce env {node with Expr = Print(arg)}) with
        | Some(env', n) ->
            match n.Expr with
            | Print(targ) ->
                // Patch the reduced AST to restore the 'PrintLn' node
                Some(env', {n with Expr = PrintLn(targ)})
            | UnitVal ->
                // The 'Print' has been fully evaluated, let'd add newline
                match env.Printer with
                | None -> None
                | Some(printer) ->
                    printer $"%s{Util.nl}"
                    Some(env', n)
            | _ -> failwith $"BUG: unexpected 'Print' reduction ${n}"
        | None -> None

    | If(cond, ifTrue, ifFalse) ->
        match cond.Expr with
        | BoolVal(v) ->
            let branch = if v then ifTrue else ifFalse
            Some(env, {node with Expr = branch.Expr})
        | _ ->
            match (reduce env cond) with
            | Some(env', cond') ->
                Some(env', {node with Expr = If(cond', ifTrue, ifFalse)})
            | None -> None

    | Seq(nodes) ->
        match nodes with
        | [] -> Some(env, {node with Expr = UnitVal})
        | [last] -> // Last node in Seq: if it's a value, we reduce to it
            if isValue last then
                Some(env, {node with Expr = last.Expr})
            else
                match (reduce env last) with
                | Some(env', last') ->
                    Some(env', {node with Expr = last'.Expr})
                | None -> None
        | first :: rest -> // Notice that here 'rest' is non-empty
            if not (isValue first) then
                match (reduce env first) with
                | Some(env', first') ->
                    Some(env', {node with Expr = Seq(first' :: rest)})
                | None -> None
            else
                Some(env, {node with Expr = Seq(rest)})

    | Type(_, _, scope) ->
        // The interpreter does not use type information at all.
        Some(env, {node with Expr = scope.Expr})

    | Ascription(_, arg) ->
        // The interpreter does not use type information at all.
        Some(env, {node with Expr = arg.Expr})

    | Assertion(arg) ->
        match arg.Expr with
        | BoolVal(true) -> Some(env, {node with Expr = UnitVal})
        | _ ->
            match (reduce env arg) with
            | Some(env', arg') ->
                Some(env', {node with Expr = Assertion(arg')})
            | None -> None

    | Let(name, init, scope) ->
        match (reduce env init) with
        | Some(env', init') ->
            Some(env', {node with Expr = Let(name, init', scope)})
        | None when (isValue init) ->
            Some(env, {node with Expr = (ASTUtil.subst scope name init).Expr})
        | None -> None

    | LetT(name, tpe, init, scope) ->
        match (reduce env init) with
        | Some(env', init') ->
            Some(env', {node with Expr = LetT(name, tpe, init', scope)})
        | None when (isValue init) ->
            Some(env, {node with Expr = (ASTUtil.subst scope name init).Expr})
        | None -> None

    | LetRec(name, tpe, init, scope) ->
        match (reduce env init) with
        | Some(env', init') ->
            Some(env', {node with Expr = LetRec(name, tpe, init', scope)})
        | None when (isValue init) ->
            let rec_init = {node with Expr = LetRec(name, tpe, init, {node with Expr = Var(name)})}
            let init' = (ASTUtil.subst init name rec_init)
            Some(env, {node with Expr = (ASTUtil.subst scope name init').Expr})
        | None -> None

    | LetMut(_, _, scope) when (isValue scope) ->
        Some(env, {node with Expr = scope.Expr})
    | LetMut(name, init, scope) ->
        match (reduce env init) with
        | Some(env', init') ->
            Some(env', {node with Expr = LetMut(name, init', scope)})
        | None when (isValue init) ->
            /// Runtime environment for reducing the 'let mutable...' scope
            let env' = {env with Mutables = env.Mutables.Add(name, init)}
            match (reduce env' scope) with
            | Some(env'', scope') ->
                /// Updated init value for the mutable variable
                let init' = env''.Mutables[name] // Crash if 'name' not found
                /// Updated runtime environment.  If the declared mutable
                /// variable 'name' was defined in the outer scope, we restore
                /// its old value (consequently, any update to the redefined
                /// variable 'name' is only visible in its scope).  Otherwise,
                /// we remove it from the updated runtime environment (so it
                /// is only visible in its scope)
                let env''' =
                    match env.Mutables.TryFind(name) with
                    | Some(v) -> {env'' with
                                    Mutables = env''.Mutables.Add(name, v)}
                    | None -> {env'' with
                                Mutables = env''.Mutables.Remove(name)}
                Some(env''', {node with Expr = LetMut(name, init', scope')})
            | None -> None
        | None -> None

    | Assign({Expr = ArrayElem(arrTarget, index)} as target, expr) when not (isValue arrTarget) ->
        match (reduce env arrTarget) with
        | Some(env', arrTarget') ->
            Some(env', {node with Expr = Assign({target with Expr = ArrayElem(arrTarget', index)}, expr)})
        | None -> None
    | Assign({Expr = ArrayElem(arrTarget, index)} as target, expr) when not (isValue index) ->
        match (reduce env index) with
        | Some(env', index') ->
            Some(env', {node with Expr = Assign({target with Expr = ArrayElem(arrTarget, index')}, expr)})
        | None -> None
    | Assign({Expr = ArrayElem _ } as target, expr) when not (isValue expr) ->
        match (reduce env expr) with
        | Some(env', expr') ->
            Some(env', {node with Expr = Assign(target, expr')})
        | None -> None
    | Assign({Expr = ArrayElem({Expr = Pointer(addr)}, index)}, value) ->
        match (env.PtrInfo.TryFind addr) with
        | Some(attrs) when attrs = ["~length"; "~data"] ->
            let arrayInstance = (env.Heap[addr].Expr, env.Heap[addr + 1u].Expr)
            match arrayInstance with
            | IntVal(length), Pointer(dataPointer) ->
                match index.Expr with
                | IntVal(i) when i >= 0 && i < length ->
                    /// Updated heap with selected array element overwritten by 'value'
                    let env' = {env with Heap = env.Heap.Add(dataPointer + (uint i), value)}
                    Some(env', value)
                | _ -> None
            | _ -> None
        | _ -> None
    | Assign({Expr = FieldSelect(selTarget, field)} as target,
             expr) when not (isValue selTarget)->
        match (reduce env selTarget) with
        | Some(env', selTarget') ->
            let target' = {target with Expr = FieldSelect(selTarget', field)}
            Some(env', {node with Expr = Assign(target', expr)})
        | None -> None
    | Assign({Expr = FieldSelect(_, _)} as target, expr) when not (isValue expr) ->
        match (reduce env expr) with
        | Some(env', expr') ->
            Some(env', {node with Expr = Assign(target, expr')})
        | None -> None
    | Assign({Expr = FieldSelect({Expr = Pointer(addr)}, field)}, value) ->
        match (env.PtrInfo.TryFind addr) with
        | Some(fields) ->
            match (List.tryFindIndex (fun f -> f = field) fields) with
            | Some(offset) ->
                /// Updated env with selected struct field overwritten by 'value'
                let env' = {env with Heap = env.Heap.Add(addr+(uint offset), value)}
                Some(env', value)
            | None -> None
        | None -> None
    | Assign(target, expr) when not (isValue expr) ->
        match (reduce env expr) with
        | Some(env', expr') ->
            Some(env', {node with Expr = Assign(target, expr')})
        | None -> None
    | Assign({Expr = Var(vname)} as target, expr) when (isValue expr)  ->
        match (env.Mutables.TryFind vname) with
        | Some _ ->
            let env' = {env with Mutables = env.Mutables.Add(vname, expr)}
            Some(env', {node with Expr = expr.Expr})
        | None -> None
    | Assign(_, _) ->
        None

    | While(cond, body) ->
        /// Rewritten 'while' loop, transformed into an 'if' on the condition
        /// 'cond'.  If 'cond' is true, we continue with the whole 'body' of the
        /// loop, followed by the whole loop itself (i.e. the node we have just
        /// matched); otherwise, when 'cond' is false, we do nothing (unit).
        let rewritten = If(cond,
                           {body with Expr = Seq([body; node])},
                           {body with Expr = UnitVal})
        Some(env, {node with Expr = rewritten})

     | DoWhile(body, cond) ->
        /// Rewritten 'DoWhile' loop, transformed into a sequence of the body
        /// followed by an 'if' on the condition. First execute the body.
        /// Then we evaluate 'cond'. If is true we continue with the whole loop again.
        /// Otherwise, when 'cond' is false we return the value produced by the last "body" execution
        let varName = Util.genSymbol "~doWhileResult"
        let rewritten = Let (varName, body,
                             {node with Expr = If(cond,
                                                {node with Expr = DoWhile(body, cond)},
                                                {body with Expr = Var(varName) })})
        Some(env, {node with Expr = rewritten})

    | Application(expr, args) ->
        match expr.Expr with
        | Lambda(lamArgs, body) ->
            if args.Length <> lamArgs.Length then None
            else
                match (reduceList env args) with
                | Some(env', args') ->
                    Some(env', {node with Expr = Application(expr, args')})
                | None ->
                    // To reduce, make sure all the arguments are values
                    if (List.forall isValue args) then
                        /// Names of lambda term arguments
                        let lamArgNames, _ = List.unzip lamArgs
                        /// Pairs of lambda term argument names with a
                        /// corresponding value (from 'args') that we are going
                        /// to substitute
                        let lamArgNamesValues = List.zip lamArgNames args
                        /// Folder function to apply a substitution over an
                        /// 'acc'umulator term.  This is used in 'body2' below
                        let folder acc (var, sub) = (ASTUtil.subst acc var sub)
                        /// Lambda term body with all substitutions applied
                        let body2 = List.fold folder body lamArgNamesValues
                        Some(env, {node with Expr = body2.Expr})
                    else None
        | _ ->
            match (reduce env expr) with
            | Some(env', expr') -> Some(env', {node with Expr = Application(expr', args)})
            | None -> None

    | StructCons(fields) ->
        let fieldNames, fieldNodes = List.unzip fields
        match (reduceList env fieldNodes) with
            | Some(env', fieldNodes') ->
                let fields' = List.zip fieldNames fieldNodes'
                Some(env', {node with Expr = StructCons(fields')})
            | None ->
                // If all struct entries are values, place them on the heap in
                // consecutive addresses
                if (List.forall isValue fieldNodes) then
                    /// Updated heap with newly-allocated struct, placed at
                    /// 'baseAddr'
                    let heap', baseAddr = heapAlloc env.Heap fieldNodes
                    /// Updated pointer info, mapping 'baseAddr' to the list of
                    /// struct field names
                    let ptrInfo' = env.PtrInfo.Add(baseAddr, fieldNames)
                    Some({env with Heap = heap'; PtrInfo = ptrInfo'},
                         {node with Expr = Pointer(baseAddr)})
                else None

    | FieldSelect({Expr = Pointer(addr)}, field) ->
        match (env.PtrInfo.TryFind addr) with
        | Some(fields) ->
            match (List.tryFindIndex (fun f -> f = field) fields) with
            | Some(offset) ->
                Some(env, env.Heap[addr + (uint offset)])
            | None -> None
        | None -> None
    | FieldSelect(target, field) when not (isValue target)->
        match (reduce env target) with
        | Some(env', target') ->
            Some(env', {node with Expr = FieldSelect(target', field)})
        | None -> None
    | FieldSelect _ -> None

    | ArrayCons(length, init) when not (isValue length) ->
        match (reduce env length) with
        | Some(env', length') ->
            Some(env', {node with Expr = ArrayCons(length', init)})
        | None -> None
    | ArrayCons(length, init) ->
        match (reduce env init) with
        | Some(env', init') ->
            Some(env', {node with Expr = ArrayCons(length, init')})
        | None when isValue init ->
            match length.Expr with
            | IntVal(l) when l > 0 ->
                /// Allocate the array on the heap, with all elements initialized, from memory `arrAddr`
                let heap', arrAddr = heapAlloc env.Heap (List.init l (fun _ -> init))

                let dataNode = { node with Expr = Pointer(arrAddr) }
                /// Updated heap with newly-allocated struct for array, placed at `baseAddr` | length + data |
                let heap'', baseAddr = heapAlloc heap' [ length; dataNode ]

                /// Update pointer info, mapping `baseAddr` to the length and data of the array
                let ptrInfo' = env.PtrInfo.Add(baseAddr, ["~length"; "~data"])
                                          .Add(arrAddr, ["~array"])
                Some({ env with Heap = heap''; PtrInfo = ptrInfo' },
                     { node with Expr = Pointer(baseAddr) })
            | _ -> None
        | None -> None

    | ArrayLength({Expr = Pointer(addr) }) ->
        match (env.PtrInfo.TryFind addr) with
        | Some(attrs) when attrs = ["~length"; "~data"] ->
            Some(env, env.Heap[addr + 0u]) // return first field in instance struct
        | _ -> None
    | ArrayLength(target) when not (isValue target) ->
        match (reduce env target) with
        | Some(env', target') ->
            Some(env', {node with Expr = ArrayLength(target')})
        | None -> None
    | ArrayLength _ -> None

    | ArrayElem ({Expr = Pointer(addr)}, {Expr = IntVal(i)}) when i >= 0 ->
        match (env.PtrInfo.TryFind addr) with
        | Some(attrs) when attrs = ["~length"; "~data"] ->
            let arrayInstance = (env.Heap[addr].Expr, env.Heap[addr + 1u].Expr)
            match arrayInstance with
            | IntVal(length), Pointer(dataPointer) when i < length ->
                Some(env, env.Heap[dataPointer + (uint i)])
            | _ -> None
        | _ -> None
    | ArrayElem(target, index) when not (isValue index) ->
        match (reduce env index) with
        | Some(env', index') ->
            Some(env', {node with Expr = ArrayElem(target, index')})
        | None -> None
    | ArrayElem(target, index) when not (isValue target) ->
        match (reduce env target) with
        | Some(env', target') ->
            Some(env', {node with Expr = ArrayElem(target', index)})
        | None -> None
    | ArrayElem _ -> None
    
    
    | Copy(arg) ->
        match (reduce env arg) with
        | Some(env', arg') -> Some(env', { node with Expr = Copy(arg') })
        | None ->
            match arg.Expr with
            | Pointer(addr) ->
                match env.PtrInfo.TryFind addr with
                | Some(fields) ->
                    // Deep copy struct by recursively copying field values
                    let fieldValues = fields |> List.mapi (fun i field ->
                        let fieldValue = env.Heap[addr + uint i]
                        // If a field is a pointer, recursively copy it
                        match fieldValue.Expr with
                        | Pointer _ ->
                            // Create a Copy expression for this field
                            let copyField = {node with Expr = Copy(fieldValue)}
                            // Recursively evaluate the Copy for this field
                            match reduce env copyField with
                            | Some(_, copyResult) -> (field, copyResult)
                            | None -> failwith $"Failed to copy nested pointer at field: {field}"
                        | _ ->
                            (field, fieldValue)) // Non-pointer fields are copied as-is

                    let deepCopy = StructCons(fieldValues)
                    Some(env, {node with Expr = deepCopy})
                | None -> None
            | _ -> None
   
             
                 
             

    | ArraySlice({ Expr = Pointer(addr) },
                 { Expr = IntVal(start) },
                 { Expr = IntVal(final) }) when start >= 0 ->
        match (env.PtrInfo.TryFind addr) with
        | Some(attrs) when attrs = ["~length"; "~data"] ->
            let arrayInstance = (env.Heap[addr].Expr, env.Heap[addr + 1u].Expr)
            match arrayInstance with
            | IntVal(length), Pointer(dataPointer) when final < length && final >= start ->
                /// Allocate the array slice struct on the heap, with data pointing at range start
                /// Since elements are in the subset of range [start, final]
                let lengthNode = { node with Expr = IntVal(final - start + 1) }
                let dataNode = { node with Expr = Pointer(dataPointer + uint start) }
                /// Updated heap with newly-allocated struct, placed at `baseAddr`
                let heap', baseAddr = heapAlloc env.Heap [ lengthNode; dataNode ]

                /// Update pointer info, mapping `baseAddr` to the length and data of the array slice
                let ptrInfo' = env.PtrInfo.Add(baseAddr, ["~length"; "~data"])
                Some({ env with Heap = heap'; PtrInfo = ptrInfo' },
                     { node with Expr = Pointer(baseAddr) })
            | _ -> None
        | _ -> None
    | ArraySlice(target, startIdx, endIdx) when not (isValue target) ->
        match (reduce env target) with
        | Some(env', target') ->
            Some(env', {node with Expr = ArraySlice(target', startIdx, endIdx)})
        | None -> None
    | ArraySlice(target, startIdx, endIdx) when not (isValue startIdx) ->
        match (reduce env startIdx) with
        | Some(env', startIdx') ->
            Some(env', {node with Expr = ArraySlice(target, startIdx', endIdx)})
        | None -> None
    | ArraySlice(target, startIdx, endIdx) when not (isValue endIdx) ->
        match (reduce env endIdx) with
        | Some(env', endIdx') ->
            Some(env', {node with Expr = ArraySlice(target, startIdx, endIdx')})
        | None -> None
    | ArraySlice _ -> None

    | UnionCons(label, expr) ->
        match (reduce env expr) with
        | Some(env', expr') -> Some(env', {node with Expr = UnionCons(label, expr')})
        | None when isValue expr ->
            /// Updated heap and base address, with union instance label
            /// followed by 'expr' (which is a value)
            let heap', baseAddr =
                heapAlloc env.Heap [{node with Expr = StringVal(label)}; expr]
            Some({env with Heap = heap'}, {node with Expr = Pointer(baseAddr)})
        | None -> None

    | Match(expr, cases) ->
        match (reduce env expr) with
        | Some(env', expr') ->
            Some(env', {node with Expr = Match(expr', cases)})
        | None when isValue expr ->
            match expr.Expr with
            | Pointer(addr) ->
                // Retrieve the label of the union instance from the heap
                match (env.Heap.TryFind addr) with
                | Some({Expr = StringVal(label)}) ->
                    // Retrieve the value of the union instance from the heap
                    match (env.Heap.TryFind (addr + 1u)) with
                    | Some(v) ->
                        // Find match case with label equal to union instance
                        match List.tryFind (fun (l,_,_) -> l = label) cases with
                        | Some(_, var, cont) ->
                            /// Continuation expression where the matched
                            /// variable is substituted by the value of the
                            /// matched union instance
                            let contSubst = ASTUtil.subst cont var v
                            Some(env, {node with Expr = contSubst.Expr})
                        | None -> None
                    | None -> None
                | _ -> None
            | _ -> None
        | None -> None

/// Attempt to reduce the given lhs, and then (if the lhs is a value) the rhs,
/// using the given runtime environment.  Return None if either (a) the lhs
/// cannot reduce, although it is not a value, or (b) the lhs is a value but the
/// rhs cannot reduce.
and internal reduceLhsRhs (env: RuntimeEnv<'E,'T>)
                          (lhs: Node<'E,'T>)
                          (rhs: Node<'E,'T>) : Option<RuntimeEnv<'E,'T> * Node<'E,'T> * Node<'E,'T>> =
    if not (isValue lhs) then
        match (reduce env lhs) with
        | Some(env', lhs') -> Some(env', lhs', rhs)
        | None -> None
    else match (reduce env rhs) with
         | Some(env', rhs') -> Some(env', lhs, rhs')
         | None -> None

/// Attempt to reduce the given list of nodes, using the given runtime
/// environment.  Proceed one node a time, following the order in the list; if a
/// node is already a value, attempt to reduce the next one.  If a reduction is
/// possible, return the updated list and environment.  Return None if (a) we
/// reach a node in the list that is stuck, or (b) the list is empty.
and internal reduceList (env: RuntimeEnv<'E,'T>)
                        (nodes: List<Node<'E,'T>>): Option<RuntimeEnv<'E,'T> * List<Node<'E,'T>>> =
    match nodes with
    | [] -> None
    | node :: rest ->
        if not (isValue node) then
            match (reduce env node) with
            | Some(env', n') -> Some(env', n' :: rest)
            | None -> None
        else
            match (reduceList env rest) with
            | Some(env', rest') -> Some(env', node :: rest')
            | None -> None

/// Allocate the given list of AST nodes (which are expected to be values) on
/// the given heap, returning the updated heap and the address where the first
/// given value is allocated.
and internal heapAlloc (heap: Heap<'E,'T>)
                       (values: List<Node<'E,'T>>): Heap<'E,'T> * uint =
    assert(values.Length <> 0) // Sanity check
    assert(List.forall isValue values) // Sanity check
    /// Compute the base address where the given values will be allocated
    let addrs = Set(heap.Keys)
    /// Maximum address already allocated on the heap
    let maxAddr: uint = if addrs.IsEmpty then 0u else addrs.MaximumElement
    /// Base address for the newly-allocated list of values
    let baseAddr = maxAddr + 1u
    /// Fold over the struct field values, adding them to the heap
    let folder (h: Heap<'E,'T>) (offset, n): Heap<'E,'T> =
        h.Add(baseAddr + uint(offset), n)
    let heap2 = List.fold folder heap (List.indexed values)
    (heap2, baseAddr)

/// Reduce the given AST until it cannot reduce further, using the given
/// (optional) 'reader' and 'writer' functions.  Return the final unreducible
/// AST node.
let rec reduceFully (node: Node<'E,'T>)
                    (reader: Option<unit -> string>)
                    (printer: Option<string -> unit>): Node<'E,'T> =
    let env = { Reader = reader;
                Printer = printer;
                Mutables = Map[];
                Heap = Map[];
                PtrInfo = Map[] }
    reduceFullyWithEnv env node
and internal reduceFullyWithEnv (env: RuntimeEnv<'E,'T>) (node: Node<'E,'T>): Node<'E,'T> =
    match (reduce env node) with
    | Some(env', node') -> reduceFullyWithEnv env' node'
    | None -> node


/// Reduce the given AST by the given number of steps, if possible.  Return the
/// resulting AST node and the number of leftover reduction steps: if greater
/// than 0, it means that the returned AST node cannot be reduced further.
let rec reduceSteps (node: Node<'E,'T>)
                    (reader: Option<unit -> string>) (printer: Option<string -> unit>)
                    (steps: int): Node<'E,'T> * int =
    let env = { Reader = reader;
                Printer = printer;
                Mutables = Map[];
                Heap = Map[];
                PtrInfo = Map[] }
    reduceStepsWithEnv env node steps
and internal reduceStepsWithEnv (env: RuntimeEnv<'E,'T>) (node: Node<'E,'T>)
                                (steps: int): Node<'E,'T> * int =
    match (reduce env node) with
    | Some(env', node') -> reduceStepsWithEnv env' node' (steps-1)
    | None -> (node, steps)


/// Is the given AST node stuck?  I.e. is it unreducible, and not a value?
let isStuck (node: Node<'E,'T>): bool =
    if (isValue node) then false
    else
        let env = { Reader = Some(fun _ -> "");
                    Printer = Some(fun _ -> ());
                    Mutables = Map[];
                    Heap = Map[];
                    PtrInfo = Map[] }
        match (reduce env node) with
         | Some(_,_) -> false
         | None -> true


/// Main interpreter function.  Reduce the given AST node until it cannot reduce
/// further; if 'verbose' is true, also print each reduction step on the console.
let interpret (node: AST.Node<'E,'T>) (verbose: bool): AST.Node<'E,'T> =
    // Reader function used when interpreting (just a regular ReadLine)
    let reader = fun (_: unit) -> System.Console.ReadLine()
    // Printer function used when interpreting (just a regular printf)
    let printer = fun str -> printf $"%s{str}"
    if not verbose then
        reduceFully node (Some reader) (Some printer)
    else
        // Internal function to verbosely interpret step-by-step.
        let rec reduceVerbosely (env: RuntimeEnv<'E,'T>)
                                (ast: AST.Node<'E,'T>): RuntimeEnv<'E,'T> * AST.Node<'E,'T> =
            Log.debug $"Runtime environment:%s{Util.nl}%O{env}"
            Log.debug $"Term to be reduced:%s{Util.nl}%s{PrettyPrinter.prettyPrint ast}"
            match (reduce env ast) with
            | Some(env', node') -> reduceVerbosely env' node'
            | None -> (env, ast)

        let env = { Reader = Some(reader);
                    Printer = Some(printer);
                    Mutables = Map[];
                    Heap = Map[];
                    PtrInfo = Map[] }
        let env', node' = reduceVerbosely env node
        node'
