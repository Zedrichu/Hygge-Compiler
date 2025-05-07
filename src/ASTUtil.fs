// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Utility functions to inspect and manipulate the Abstract Syntax Tree of
/// Hygge programs.
module ASTUtil

open AST
open Log
open PrettyPrinter

/// Given the AST 'node', return a new AST node where every free occurrence of
/// the variable called 'var' is substituted by the AST node 'sub'.
let rec subst (node: Node<'E,'T>) (var: string) (sub: Node<'E,'T>): Node<'E,'T> =
    match node.Expr with
    | UnitVal
    | IntVal(_)
    | BoolVal(_)
    | FloatVal(_)
    | StringVal(_) -> node // The substitution has no effect

    | Pointer(_) -> node // The substitution has no effect

    | Var(vname) when vname = var -> sub // Substitution applied
    | Var(_) -> node // The substitution has no effect

    | Add(lhs, rhs) ->
        {node with Expr = Add((subst lhs var sub), (subst rhs var sub))}
    | Sub(lhs, rhs) ->
        {node with Expr = Sub((subst lhs var sub), (subst rhs var sub))}
    | Mult(lhs, rhs) ->
        {node with Expr = Mult((subst lhs var sub), (subst rhs var sub))}
    | Div(lhs, rhs) ->
        {node with Expr = Div((subst lhs var sub), (subst rhs var sub))}
    | Mod(lhs, rhs) ->
        {node with Expr = Mod((subst lhs var sub), (subst rhs var sub))}
    | Sqrt(arg) ->
        {node with Expr = Sqrt(subst arg var sub)}
    | Min(lhs, rhs) ->
        {node with Expr = Min((subst lhs var sub), (subst rhs var sub))}
    | Max(lhs, rhs) ->
        {node with Expr = Max((subst lhs var sub), (subst rhs var sub))}

    | And(lhs, rhs) ->
        {node with Expr = And((subst lhs var sub), (subst rhs var sub))}
    | Or(lhs, rhs) ->
        {node with Expr = Or((subst lhs var sub), (subst rhs var sub))}
    | Not(arg) ->
        {node with Expr = Not(subst arg var sub)}

    | Eq(lhs, rhs) ->
        {node with Expr = Eq((subst lhs var sub), (subst rhs var sub))}
    | Less(lhs, rhs) ->
        {node with Expr = Less((subst lhs var sub), (subst rhs var sub))}
    | Greater(lhs, rhs) ->
        {node with Expr = Greater((subst lhs var sub), (subst rhs var sub))}
    | LessEq(lhs, rhs) ->
        {node with Expr = LessEq((subst lhs var sub), (subst rhs var sub))}
    | GreaterEq(lhs, rhs) ->
        {node with Expr = GreaterEq((subst lhs var sub), (subst rhs var sub))}
    | ReadInt
    | ReadFloat -> node // The substitution has no effect

    | Print(arg) ->
        {node with Expr = Print(subst arg var sub)}
    | PrintLn(arg) ->
        {node with Expr = PrintLn(subst arg var sub)}

    | If(cond, ifTrue, ifFalse) ->
        {node with Expr = If((subst cond var sub), (subst ifTrue var sub),
                                                   (subst ifFalse var sub))}

    | Seq(nodes) ->
        let substNodes = List.map (fun n -> (subst n var sub)) nodes
        {node with Expr = Seq(substNodes)}

    | Type(tname, def, scope) ->
        {node with Expr = Type(tname, def, (subst scope var sub))}

    | Ascription(tpe, node) ->
        {node with Expr = Ascription(tpe, (subst node var sub))}

    | Assertion(arg) ->
        {node with Expr = Assertion(subst arg var sub)}

    | Let(vname, init, scope) when vname = var ->
        // The variable is shadowed, do not substitute it in the "let" scope
        {node with Expr = Let(vname, (subst init var sub), scope)}
    | Let(vname, init, scope) ->
        // Propagate the substitution in the "let" scope
        {node with Expr = Let(vname, (subst init var sub),
                              (subst scope var sub))}

    | LetT(vname, tpe, init, scope) when vname = var ->
        // The variable is shadowed, do not substitute it in the "let" scope
        {node with Expr = LetT(vname, tpe, (subst init var sub), scope)}
    | LetT(vname, tpe, init, scope) ->
        // Propagate the substitution in the "let" scope
        {node with Expr = LetT(vname, tpe, (subst init var sub),
                               (subst scope var sub))}

    | LetRec(vname, tpe, init, scope) when vname = var ->
        // The variable is shadowed, do not substitute it in the "let rec" scope
        // and similarly in "let rec" initialisation as it might be recursively defined
        node
    | LetRec(vname, tpe, init, scope) ->
        // Propagate the substitution in the "let rec" scope and init safely
        {node with Expr = LetRec(vname, tpe, (subst init var sub),
                                 (subst scope var sub))}

    | LetMut(vname, init, scope) when vname = var ->
        // Do not substitute the variable in the "let mutable" scope
        {node with Expr = LetMut(vname, (subst init var sub), scope)}
    | LetMut(vname, init, scope) ->
        {node with Expr = LetMut(vname, (subst init var sub),
                                 (subst scope var sub))}

    | Assign(target, expr) ->
        {node with Expr = Assign((subst target var sub), (subst expr var sub))}

    | While(cond, body) ->
        let substCond = subst cond var sub
        let substBody = subst body var sub
        {node with Expr = While(substCond, substBody)}

    | DoWhile(body, cond) ->
        let substBody = subst body var sub
        let substCond = subst cond var sub
        {node with Expr = DoWhile(substBody, substCond)}

    | Lambda(args, body) ->
        /// Arguments of this lambda term, without their pretypes
        let (argVars, _) = List.unzip args
        if (List.contains var argVars) then node // No substitution
        else {node with Expr = Lambda(args, (subst body var sub))}

    | Application(expr, args) ->
        let substExpr = subst expr var sub
        let substArgs = List.map (fun n -> (subst n var sub)) args
        {node with Expr = Application(substExpr, substArgs)}

    | StructCons(fields) ->
        let (fieldNames, initNodes) = List.unzip fields
        let substInitNodes = List.map (fun e -> (subst e var sub)) initNodes
        {node with Expr = StructCons(List.zip fieldNames substInitNodes)}

    | FieldSelect(target, field) ->
        {node with Expr = FieldSelect((subst target var sub), field)}

    | ArrayCons(length, init) ->
        {node with Expr = ArrayCons((subst length var sub), (subst init var sub))}

    | ArrayLength(target) ->
        {node with Expr = ArrayLength(subst target var sub)}

    | ArrayElem(target, index) ->
        {node with Expr = ArrayElem((subst target var sub), (subst index var sub))}

    | ArraySlice(target, startIdx, endIdx) ->
        {node with Expr = ArraySlice((subst target var sub),
                                     (subst startIdx var sub),
                                     (subst endIdx var sub))}
    | UnionCons(label, expr) ->
        {node with Expr = UnionCons(label, (subst expr var sub))}

    | Match(expr, cases) ->
        /// Mapper function to propagate the substitution along a match case
        let substCase(lab: string, v: string, cont: Node<'E,'T>) =
            if (v = var) then (lab, v, cont) // Variable bound, no substitution
            else (lab, v, (subst cont var sub))
        let cases2 = List.map substCase cases
        {node with Expr = Match((subst expr var sub), cases2)}

/// Compute the set of free variables in the given AST node.
let rec freeVars (node: Node<'E,'T>): Set<string> =
    match node.Expr with
    | UnitVal
    | IntVal(_)
    | BoolVal(_)
    | FloatVal(_)
    | StringVal(_)
    | Pointer(_) -> Set[]
    | Var(name) -> Set[name]
    | Sub(lhs, rhs)
    | Div(lhs, rhs)
    | Mod(lhs, rhs)
    | Add(lhs, rhs)
    | Mult(lhs, rhs) ->
        Set.union (freeVars lhs) (freeVars rhs)
    | Not(arg)
    | Sqrt(arg) -> freeVars arg
    | And(lhs, rhs)
    | Or(lhs, rhs) ->
        Set.union (freeVars lhs) (freeVars rhs)
    | Eq(lhs, rhs)
    | Min(lhs, rhs)
    | Max(lhs, rhs)
    | Greater(lhs, rhs)
    | LessEq(lhs, rhs)
    | GreaterEq(lhs, rhs)
    | Less(lhs, rhs) ->
        Set.union (freeVars lhs) (freeVars rhs)
    | ReadInt
    | ReadFloat -> Set[]
    | Print(arg)
    | PrintLn(arg) -> freeVars arg
    | If(condition, ifTrue, ifFalse) ->
        Set.union (freeVars condition)
                  (Set.union (freeVars ifTrue) (freeVars ifFalse))
    | Seq(nodes) -> freeVarsInList nodes
    | Ascription(_, node) -> freeVars node
    | Let(name, init, scope)
    | LetT(name, _, init, scope)
    | LetMut(name, init, scope) ->
        // All the free variables in the 'let' initialisation, together with all
        // free variables in the scope --- minus the newly-bound variable
        Set.union (freeVars init) (Set.remove name (freeVars scope))
    | Assign(target, expr) ->
        // Union of the free names of the lhs and the rhs of the assignment
        Set.union (freeVars target) (freeVars expr)
    | DoWhile(body, cond)
    | While(cond, body) -> Set.union (freeVars cond) (freeVars body)
    | Assertion(arg) -> freeVars arg
    | Type(_, _, scope) -> freeVars scope
    | Lambda(args, body) ->
        let (argNames, _) = List.unzip args
        // All the free variables in the lambda function body, minus the
        // names of the arguments
        Set.difference (freeVars body) (Set.ofList argNames)
    | Application(expr, args) ->
        let fvArgs = List.map freeVars args
        // Union of free variables in the applied expr, plus all its arguments
        Set.union (freeVars expr) (freeVarsInList args)
    | StructCons(fields) ->
        let (_, nodes) = List.unzip fields
        freeVarsInList nodes
    | FieldSelect(expr, _) -> freeVars expr
    | LetRec(name, _, init, scope) ->
        // Remove the newly-bound variable from the free variables of both
        // init and scope since it might be recursively referenced in init
        Set.remove name (Set.union (freeVars init) (freeVars scope))
    | ArrayCons(length, init) ->
        Set.union (freeVars length) (freeVars init)
    | ArrayLength(target) -> freeVars target
    | ArrayElem(target, index) ->
        Set.union (freeVars target) (freeVars index)
    | ArraySlice(target, startIdx, endIdx) ->
        Set.union (freeVars target)
                  (Set.union (freeVars startIdx) (freeVars endIdx))
    | UnionCons(_, expr) -> freeVars expr
    | Match(expr, cases) ->
        /// Compute the free variables in all match cases continuations, minus
        /// the variable bound in the corresponding match case.  This 'folder'
        /// is used to fold over all match cases.
        let folder (acc: Set<string>) (_, var, cont: Node<'E,'T>): Set<string> =
            Set.union acc ((freeVars cont).Remove var)
        /// Free variables in all match continuations
        let fvConts = List.fold folder Set[] cases
        Set.union (freeVars expr) fvConts

/// Compute the union of the free variables in a list of AST nodes.
and internal freeVarsInList (nodes: List<Node<'E,'T>>): Set<string> =
    /// Compute the free variables of 'node' and add them to the accumulator
    let folder (acc: Set<string>) (node: Node<'E,'T> ) =
        Set.union acc (freeVars node)
    List.fold folder Set[] nodes


/// Compute the set of captured variables in the given AST node.
let rec capturedVars (node: Node<'E,'T>): Set<string> =
    match node.Expr with
    | UnitVal
    | IntVal(_)
    | BoolVal(_)
    | FloatVal(_)
    | StringVal(_)
    | Pointer(_)
    | Lambda _ ->
        // All free variables of a value are considered as captured
        freeVars node
    | Var(_) -> Set[]
    | Add(lhs, rhs)
    | Sub(lhs, rhs)
    | Div(lhs, rhs)
    | Mod(lhs, rhs)
    | Mult(lhs, rhs) ->
        Set.union (capturedVars lhs) (capturedVars rhs)
    | Not(arg)
    | Sqrt(arg) -> capturedVars arg
    | And(lhs, rhs)
    | Or(lhs, rhs) ->
        Set.union (capturedVars lhs) (capturedVars rhs)
    | Min(lhs, rhs)
    | Max(lhs, rhs)
    | Greater(lhs, rhs)
    | LessEq(lhs, rhs)
    | GreaterEq(lhs, rhs)
    | Eq(lhs, rhs)
    | Less(lhs, rhs) ->
        Set.union (capturedVars lhs) (capturedVars rhs)
    | ReadInt
    | ReadFloat -> Set[]
    | Print(arg)
    | PrintLn(arg) -> capturedVars arg
    | If(condition, ifTrue, ifFalse) ->
        Set.union (capturedVars condition)
                  (Set.union (capturedVars ifTrue) (capturedVars ifFalse))
    | Seq(nodes) -> capturedVarsInList nodes
    | Ascription(_, node) -> capturedVars node
    | Let(name, init, scope)
    | LetT(name, _, init, scope)
    | LetMut(name, init, scope) ->
        // All the captured variables in the 'let' initialisation, together with
        // all captured variables in the scope --- minus the newly-bound var
        Set.union (capturedVars init) (Set.remove name (capturedVars scope))
    | Assign(target, expr) ->
        // Union of the captured vars of the lhs and the rhs of the assignment
        Set.union (capturedVars target) (capturedVars expr)
    | DoWhile(body, cond)
    | While(cond, body) -> Set.union (capturedVars cond) (capturedVars body)
    | Assertion(arg) -> capturedVars arg
    | Type(_, _, scope) -> capturedVars scope
    | Application(expr, args) ->
        let fvArgs = List.map capturedVars args
        // Union of captured variables in the applied expr, plus all arguments
        Set.union (capturedVars expr) (capturedVarsInList args)
    | StructCons(fields) ->
        let (_, nodes) = List.unzip fields
        capturedVarsInList nodes
    | FieldSelect(expr, _) -> capturedVars expr
    | LetRec(name, _, init, scope) ->
        // Remove the newly-bound variable from the captured variables of both
        // init and scope since it might be recursively referenced in init
        Set.remove name (Set.union (capturedVars init) (capturedVars scope))
    | ArrayCons(length, init) ->
        Set.union (capturedVars length) (capturedVars init)
    | ArrayLength(target) -> capturedVars target
    | ArrayElem(target, index) ->
        Set.union (capturedVars target) (capturedVars index)
    | ArraySlice(target, startIdx, endIdx) ->
        Set.union (capturedVars target)
                  (Set.union (capturedVars startIdx) (capturedVars endIdx))
    | UnionCons(_, expr) -> capturedVars expr
    | Match(expr, cases) ->
        /// Compute the captured variables in all match cases continuations,
        /// minus the variable bound in the corresponding match case.  This
        /// 'folder' is used to fold over all match cases.
        let folder (acc: Set<string>) (_, var, cont: Node<'E,'T>): Set<string> =
            Set.union acc ((capturedVars cont).Remove var)
        /// Captured variables in all match continuations
        let cvConts = List.fold folder Set[] cases
        Set.union (capturedVars expr) cvConts

/// Compute the union of the captured variables in a list of AST nodes.
and internal capturedVarsInList (nodes: List<Node<'E,'T>>): Set<string> =
    /// Compute the free variables of 'node' and add them to the accumulator
    let folder (acc: Set<string>) (node: Node<'E,'T> ) =
        Set.union acc (capturedVars node)
    List.fold folder Set[] nodes

let mapUnion (map1: Map<'K, 'V>) (map2: Map<'K, 'V>) =
    Map.fold (fun acc key value -> Map.add key value acc) map1 map2

let mapDifference (map1: Map<'Key, 'T>) (map2: Map<'Key, 'U>) =
    Map.filter (fun k _ -> not (Map.containsKey k map2)) map1

/// Compute the set of free variables in the given AST node.  
/// (parentExpr, node) -> Map[name, (parentExpr, node)]
let rec freeVarsMap (parentNode: Node<'E,'T>) (node: Node<'E,'T>): Map<string,(Node<'E,'T> * Node<'E,'T>)> =
    match node.Expr with
    | UnitVal
    | IntVal(_)
    | BoolVal(_)
    | FloatVal(_)
    | StringVal(_)
    | Pointer(_) -> Map[]
    | Var(name) -> Map [(name, (parentNode, node))]
    | Sub(lhs, rhs)
    | Div(lhs, rhs)
    | Mod(lhs, rhs)
    | Add(lhs, rhs)
    | Mult(lhs, rhs) ->
        mapUnion (freeVarsMap node lhs) (freeVarsMap node rhs)
        // Set.union (freeVarsNode lhs) (freeVarsNode rhs)
    | Not(arg)
    | Sqrt(arg) -> freeVarsMap node arg
    | And(lhs, rhs)
    | Or(lhs, rhs) ->
        mapUnion (freeVarsMap node lhs) (freeVarsMap node rhs)
        // Set.union (freeVarsNode lhs) (freeVarsNode rhs)
    | Eq(lhs, rhs)
    | Min(lhs, rhs)
    | Max(lhs, rhs)
    | Greater(lhs, rhs)
    | LessEq(lhs, rhs)
    | GreaterEq(lhs, rhs)
    | Less(lhs, rhs) ->
        mapUnion (freeVarsMap node lhs) (freeVarsMap node rhs)
        // Set.union (freeVarsNode lhs) (freeVarsNode rhs)
    | ReadInt
    | ReadFloat -> Map[]
    | Print(arg)
    | PrintLn(arg) -> freeVarsMap node arg
    | If(condition, ifTrue, ifFalse) ->
        mapUnion (freeVarsMap node condition)
                  (mapUnion (freeVarsMap node ifTrue) (freeVarsMap node ifFalse))
    | Seq(nodes) -> freeVarsInListNode node nodes
    | Ascription(_, node) -> freeVarsMap node node
    | Let(name, init, scope)
    | LetT(name, _, init, scope)
    | LetMut(name, init, scope) ->
        // All the free variables in the 'let' initialisation, together with all
        // free variables in the scope --- minus the newly-bound variable
        mapUnion (freeVarsMap node init) (Map.remove name (freeVarsMap node scope))
    | Assign(target, expr) ->
        // Union of the free names of the lhs and the rhs of the assignment
        mapUnion (freeVarsMap node target) (freeVarsMap node expr)
    | DoWhile(body, cond)
    | While(cond, body) -> mapUnion (freeVarsMap node cond) (freeVarsMap node body)
    | Assertion(arg) -> freeVarsMap node arg
    | Type(_, _, scope) -> freeVarsMap node scope
    | Lambda(args, body) ->
        let (argNames, _) = List.unzip args
        let zipped = List.zip argNames (List.map (fun argName -> Var(argName)) argNames)
        // All the free variables in the lambda function body, minus the
        // names of the arguments
        mapDifference (freeVarsMap node body) (Map.ofList zipped)
    | Application(expr, args) ->
        // Union of free variables in the applied expr, plus all its arguments

        // Keep parent node the same for subsequent Application nodes
        // such that a full "application" sequence is used when showing computed value
        match parentNode.Expr with
        | Application(_, _) ->
            mapUnion (freeVarsMap parentNode expr) (freeVarsInListNode parentNode args)
        | _ ->
            mapUnion (freeVarsMap node expr) (freeVarsInListNode node args)
    | StructCons(fields) ->
        let (_, nodes) = List.unzip fields
        freeVarsInListNode node nodes
    | FieldSelect(expr, _) -> freeVarsMap node expr
    | LetRec(name, _, init, scope) ->
        // Remove the newly-bound variable from the free variables of both
        // init and scope since it might be recursively referenced in init
        Map.remove name (mapUnion (freeVarsMap node init) (freeVarsMap node scope))
    | ArrayCons(length, init) ->
        mapUnion (freeVarsMap node length) (freeVarsMap node init)
    | ArrayLength(target) -> freeVarsMap node target
    | ArrayElem(target, index) ->
        mapUnion (freeVarsMap node target) (freeVarsMap node index)
    | ArraySlice(target, startIdx, endIdx) ->
        mapUnion (freeVarsMap node target)
                  (mapUnion (freeVarsMap node startIdx) (freeVarsMap node endIdx))
    | UnionCons(_, expr) -> freeVarsMap node expr
    | Match(expr, cases) ->
        /// Compute the free variables in all match cases continuations, minus
        /// the variable bound in the corresponding match case.  This 'folder'
        /// is used to fold over all match cases.
        let folder (acc: Map<string, (Node<'E,'T> * Node<'E,'T>)>) (_, var, cont: Node<'E,'T>): Map<string, Node<'E,'T> * Node<'E,'T>> =
            mapUnion acc ((freeVarsMap node cont).Remove var)
        /// Free variables in all match continuations
        let fvConts: Map<string,(Node<'E,'T> * Node<'E,'T>)> = List.fold folder Map[] cases
        mapUnion (freeVarsMap node expr) fvConts

/// Compute the union of the free variables in a list of AST nodes.
and internal freeVarsInListNode (parentNode: Node<'E,'T>) (nodes: List<Node<'E,'T>>): Map<string,Node<'E,'T> * Node<'E,'T>> =
    /// Compute the free variables of 'node' and add them to the accumulator
    let folder (acc: Map<string, Node<'E,'T> * Node<'E,'T>>) (node: Node<'E,'T> ) =
        mapUnion acc (freeVarsMap parentNode node)
    List.fold folder Map[] nodes

let rec decorateAssertions (node: Node<'E,'T>): Node<'E,'T> =
    match node.Expr with
    | UnitVal
    | IntVal(_)
    | BoolVal(_)
    | FloatVal(_)
    | StringVal(_) -> node // The substitution has no effect

    | Pointer(_) -> node // The substitution has no effect

    | Var(_) -> node // The substitution has no effect

    | Add(lhs, rhs) ->
        {node with Expr = Add((decorateAssertions lhs), (decorateAssertions rhs))}
    | Sub(lhs, rhs) ->
        {node with Expr = Sub((decorateAssertions lhs), (decorateAssertions rhs))}
    | Mult(lhs, rhs) ->
        {node with Expr = Mult((decorateAssertions lhs), (decorateAssertions rhs))}
    | Div(lhs, rhs) ->
        {node with Expr = Div((decorateAssertions lhs), (decorateAssertions rhs))}
    | Mod(lhs, rhs) ->
        {node with Expr = Mod((decorateAssertions lhs), (decorateAssertions rhs))}
    | Sqrt(arg) ->
        {node with Expr = Sqrt(decorateAssertions arg)}
    | Min(lhs, rhs) ->
        {node with Expr = Min((decorateAssertions lhs), (decorateAssertions rhs))}
    | Max(lhs, rhs) ->
        {node with Expr = Max((decorateAssertions lhs), (decorateAssertions rhs))}

    | And(lhs, rhs) ->
        {node with Expr = And((decorateAssertions lhs), (decorateAssertions rhs))}
    | Or(lhs, rhs) ->
        {node with Expr = Or((decorateAssertions lhs), (decorateAssertions rhs))}
    | Not(arg) ->
        {node with Expr = Not(decorateAssertions arg)}

    | Eq(lhs, rhs) ->
        {node with Expr = Eq((decorateAssertions lhs), (decorateAssertions rhs))}
    | Less(lhs, rhs) ->
        {node with Expr = Less((decorateAssertions lhs), (decorateAssertions rhs))}
    | Greater(lhs, rhs) ->
        {node with Expr = Greater((decorateAssertions lhs), (decorateAssertions rhs))}
    | LessEq(lhs, rhs) ->
        {node with Expr = LessEq((decorateAssertions lhs), (decorateAssertions rhs))}
    | GreaterEq(lhs, rhs) ->
        {node with Expr = GreaterEq((decorateAssertions lhs), (decorateAssertions rhs))}
    | ReadInt
    | ReadFloat -> node // The substitution has no effect

    | Print(arg) ->
        {node with Expr = Print(decorateAssertions arg)}
    | PrintLn(arg) ->
        {node with Expr = PrintLn(decorateAssertions arg)}

    | If(cond, ifTrue, ifFalse) ->
        {node with Expr = If((decorateAssertions cond), (decorateAssertions ifTrue),
                                                   (decorateAssertions ifFalse))}

    | Seq(nodes) ->
        let substNodes = List.map (fun n -> (decorateAssertions n)) nodes
        {node with Expr = Seq(substNodes)}

    | Type(tname, def, scope) ->
        {node with Expr = Type(tname, def, (decorateAssertions scope))}

    | Ascription(tpe, node) ->
        {node with Expr = Ascription(tpe, (decorateAssertions node))}

    | Assertion(arg) ->
        // Recursively decorate the argument to process nested assertions
        let decoratedArg = decorateAssertions arg

        /// Get the last nested expression (last Seq or Let scope) 
        /// since it is the expression which effectively decides on the assertion failure
        let rec getKeyNodeFolder (node: Node<'E,'T>) =
            match node.Expr with
            | Seq(nodes) ->
                getKeyNodeFolder nodes[nodes.Length - 1]
            | Let(_, _, scope)
            | LetT(_, _, _, scope)
            | LetMut(_, _, scope)
            | LetRec(_, _, _, scope) ->
                getKeyNodeFolder scope
            | _ -> node

        let keyNode = getKeyNodeFolder arg

        /// Get free variables in the keyNode
        /// Having keyNode as an argument we ensure that the nested variable declarations
        /// will be included in the printout if they were referenced in the key assertion calculation
        let fvList = Map.toList (freeVarsMap node keyNode)

        let constructSimpleVarPrint (node: Node<'E,'T>) (varName: string) (varExpr: Expr<'E,'T>) =
            [{ node with Expr = Print({ node with Expr = StringVal($" - {varName} = ") }) };
             { node with Expr = PrintLn({ node with Expr = varExpr }) }]

        /// Create print nodes for each free variable
        let printVarNodes =
            fvList |> List.collect (fun (record: string * (Node<'E,'T> * Node<'E,'T>)) ->
                let (varName: string, (parentNode: Node<'E,'T>, varNode: Node<'E,'T>)) = record
                Log.debug $"{varName}::{varNode}::{parentNode}"

                // TODO: consider recursive processing for nested expressions or simplify reporting

                match parentNode.Expr with
                // TODO: interpreter print struct
                // | FieldSelect(node, field) (print whole struct instead)
                | Application(node, args) ->
                    match node.Expr with
                    | Var(name) when name <> varName ->
                        constructSimpleVarPrint node varName varNode.Expr
                    | _ -> 
                        constructSimpleVarPrint 
                            node
                            (
                                let sourceCode = SourceRepository.repository.GetSnippet(
                                    parentNode.Pos,
                                    parentNode.Pos,
                                    false,
                                    false,
                                    false )
                                match sourceCode with
                                | Some strArr ->
                                    " - " + List.reduce (fun acc el -> acc + el.Trim()) strArr
                                | None ->
                                    match args.Length with
                                    | 0 -> $" - {varName}()"
                                    | _ -> $" - {varName}(...)" )
                            parentNode.Expr
                | ArrayLength(node) ->
                    match node.Expr with
                    | Var(name) -> 
                        [
                            { node with Expr = Print({ node with Expr = StringVal($" - arrayLength({name}) = ") }) };
                            { node with Expr = PrintLn({ node with Expr = parentNode.Expr }) }
                        ]
                    | _ -> 
                        [
                            { node with Expr = Print({ node with Expr = StringVal($" - arrayLength({node.Pos.FileName}:({node.Pos.LineStart}:{node.Pos.ColStart}-{node.Pos.LineEnd}:{node.Pos.ColEnd})) = ") }) };
                            { node with Expr = PrintLn({ node with Expr = parentNode.Expr }) }
                        ]
                | ArrayElem(node, index) when varNode.Expr = node.Expr ->
                    match node.Expr with
                    | Var(name) ->
                        [
                            { node with Expr = Print({ node with Expr = StringVal($" - arrayElem({name}, ") }) };
                            { node with Expr = Print(index) };
                            { node with Expr = Print({ node with Expr = StringVal(") = ") }) };
                            { node with Expr = PrintLn({ node with Expr = parentNode.Expr }) }
                        ]
                    | _ -> 
                        [
                            { node with Expr = Print({ node with Expr = StringVal($" - arrayElem({node.Pos.FileName}:({node.Pos.LineStart}:{node.Pos.ColStart}-{node.Pos.LineEnd}:{node.Pos.ColEnd}), ") }) };
                            { node with Expr = Print(index) };
                            { node with Expr = Print({ node with Expr = StringVal(") = ") }) };
                            { node with Expr = PrintLn({ node with Expr = parentNode.Expr }) }
                        ]
                | ArraySlice(node, startIdx, endIdx) ->
                    // debug $"({node.Expr}[{startIdx}:{endIdx}])"
                    // ($"({node.Expr}[{startIdx}:{endIdx}])", parentExpr)
                    []
                | UnionCons(label, node) ->
                    // debug $"({node.Expr}::{label})"
                    // Some ($"({node.Expr}::{label})", parentExpr)
                    []
                | _ -> constructSimpleVarPrint node varName varNode.Expr
            )

        /// Prepare code snippet to be shown
        let snippet = SourceRepository.repository.GetSnippet(
            node.Pos, 
            keyNode.Pos,
            true, 
            true,
            true
        )
        let msgArr =
            match snippet with
            | Some strArr -> List.concat [
                [""];
                ["***********************"];
                [$"Assertion error @ {node.Pos.FileName}:{node.Pos.LineStart}:{node.Pos.ColStart}"];
                ["-----------------------"];
                strArr;
                ["-----------------------"];
                ["Relevant Variables:"]]
            | None -> List.concat [
                [""];
                ["***********************"];
                ["Assertion failed: <no source available>"];
                ["-----------------------"];
                ["Relevant Variables:"]]

        /// Create header node with source code and location information 
        let msgArrAst = (List.map (fun el -> { node with Expr = PrintLn({ node with Expr = StringVal el }) }) msgArr)

        /// Printing should be inserted just before the "key node" in the AST
        /// such that the context is the same and the assertion result is not changed
        let rec annotateKeyNode (node: Node<'E,'T>) =
            match node.Expr with
            | Seq(nodes) ->
                { node with Expr = Seq(nodes[0..nodes.Length - 2] @ [annotateKeyNode nodes[nodes.Length - 1]]) }
            | Let(name, init, scope)
            | LetT(name, _, init, scope)
            | LetMut(name, init, scope)
            | LetRec(name, _, init, scope) ->
                {node with Expr = Let(name, init, (annotateKeyNode scope))}
            | _ -> 
                { node with Expr = Seq(
                                msgArrAst @
                                printVarNodes @
                                [{ node with Expr = PrintLn({ node with Expr = StringVal "***********************" }) }] @
                                [node]) }

        // Wrap annotated AST in Assertion expression
        let failureBranch = { node with Expr = Assertion(annotateKeyNode arg) }

        // Create the success case (Unit)
        let successBranch = { node with Expr = UnitVal }

        // Create the Not(decoratedArg) node
        // The decoratedArg should be used instead of arg 
        // to ensure nested assertion error reporting
        let condition = { node with Expr = Not(decoratedArg) }

        let res = { node with Expr = If(condition, failureBranch, successBranch) }
        Log.info (prettyPrint res)
        res

    | Let(vname, init, scope) ->
        // Propagate the substitution in the "let" scope
        {node with Expr = Let(vname, (decorateAssertions init),
                              (decorateAssertions scope))}

    | LetT(vname, tpe, init, scope) ->
        // Propagate the substitution in the "let" scope
        {node with Expr = LetT(vname, tpe, (decorateAssertions init),
                               (decorateAssertions scope))}

    | LetRec(vname, tpe, init, scope) ->
        // Propagate the substitution in the "let rec" scope and init safely
        {node with Expr = LetRec(vname, tpe, (decorateAssertions init),
                                 (decorateAssertions scope))}

    | LetMut(vname, init, scope) ->
        {node with Expr = LetMut(vname, (decorateAssertions init),
                                 (decorateAssertions scope))}

    | Assign(target, expr) ->
        {node with Expr = Assign((decorateAssertions target), (decorateAssertions expr))}

    | While(cond, body) ->
        let substCond = decorateAssertions cond
        let substBody = decorateAssertions body
        {node with Expr = While(substCond, substBody)}

    | DoWhile(body, cond) ->
        let substBody = decorateAssertions body
        let substCond = decorateAssertions cond
        {node with Expr = DoWhile(substBody, substCond)}

    | Lambda(args, body) ->
        {node with Expr = Lambda(args, (decorateAssertions body))}

    | Application(expr, args) ->
        let substExpr = decorateAssertions expr
        let substArgs = List.map (fun n -> (decorateAssertions n)) args
        {node with Expr = Application(substExpr, substArgs)}

    | StructCons(fields) ->
        let (fieldNames, initNodes) = List.unzip fields
        let substInitNodes = List.map (fun e -> (decorateAssertions e)) initNodes
        {node with Expr = StructCons(List.zip fieldNames substInitNodes)}

    | FieldSelect(target, field) ->
        {node with Expr = FieldSelect((decorateAssertions target), field)}

    | ArrayCons(length, init) ->
        {node with Expr = ArrayCons((decorateAssertions length), (decorateAssertions init))}

    | ArrayLength(target) ->
        {node with Expr = ArrayLength(decorateAssertions target)}

    | ArrayElem(target, index) ->
        {node with Expr = ArrayElem((decorateAssertions target), (decorateAssertions index))}

    | ArraySlice(target, startIdx, endIdx) ->
        {node with Expr = ArraySlice((decorateAssertions target),
                                     (decorateAssertions startIdx),
                                     (decorateAssertions endIdx))}
    | UnionCons(label, expr) ->
        {node with Expr = UnionCons(label, (decorateAssertions expr))}

    | Match(expr, cases) ->
        /// Mapper function to propagate the substitution along a match case
        let substCase(lab: string, v: string, cont: Node<'E,'T>) =
            (lab, v, (decorateAssertions cont))
        let cases2 = List.map substCase cases
        {node with Expr = Match((decorateAssertions expr), cases2)}