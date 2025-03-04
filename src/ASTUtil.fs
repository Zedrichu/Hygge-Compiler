// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Utility functions to inspect and manipulate the Abstract Syntax Tree of
/// Hygge programs.
module ASTUtil

open AST


/// Given the AST 'node', return a new AST node where every free occurrence of
/// the variable called 'var' is substituted by the AST node 'sub'.
let rec subst (node: Node<'E,'T>) (var: string) (sub: Node<'E,'T>): Node<'E,'T> =
    match node.Expr with
    | UnitVal
    | IntVal(_)
    | BoolVal(_)
    | FloatVal(_)
    | StringVal(_) -> node // The substitution has no effect

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
