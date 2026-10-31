// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Functions to perform peephole optimizations on RISC-V assembly code.
module Peephole

open RISCV


/// Optimize a list of Text segment statements.
let rec internal optimizeText (text: List<TextStmt>): List<TextStmt> =
    match text with
    // If a small-enough constant integer is loaded and then added, perform
    // a direct `addi` operation instead
    | (RV.LI(rd1, value), comment1) ::
      (RV.ADD(rd2, rs1, rs2), comment2) ::
      rest when rd1 = rs2 && (isImm12 value) ->
        (RV.LI(rd1, value), comment1) ::
        (RV.ADDI(rd2, rs1, Imm12(value)), comment2) ::
        optimizeText rest

    // Strength reduction
    | (RV.LI(rd1, value), comment1) ::
      (RV.MUL(rd2, rs1, rs2), comment2) ::
      rest when value = 2 && rd1 = rs2 ->
        (RV.LI(rd1, value), comment1) ::
        (RV.SLLI(rd2, rs1, Shamt(1u)), comment2) ::
        optimizeText rest

    | (RV.LI(rd1, value), comment1) ::
      (RV.DIV(rd2, rs1, rs2), comment2) ::
      rest when value = 64 && rd1 = rs2 ->
        (RV.LI(rd1, value), comment1) ::
        (RV.SRAI(rd2, rs1, Shamt(6u)), comment2) ::
        optimizeText rest

    // Removal of redundant assignments
    | (RV.MV(rd1, rs1), comment1) ::
      (RV.MV(rd2, rs2), comment2) ::
      rest when rd1 = rs2 && rd2 = rs1 ->
        (RV.MV(rd1, rd2), $"{comment1} {comment2}") ::
        optimizeText rest

    | (RV.MV(rd1, rs1), comment1) ::
      (RV.LI(rd2, value), comment2) ::
      rest when rd1 = rd2 && (isImm12 value) ->
        (RV.LI(rd1, value), $"{comment1} {comment2}") ::
        optimizeText rest

    | stmt :: rest ->
        // If we are here, we did not find any pattern to optimize: we skip the
        // first assembly statement and try with the rest
        stmt :: (optimizeText rest)

    | [] -> []


/// Optimize the given assembly code.
let optimize (asm: Asm): Asm =
    Log.info "Starting peephole optimization"
    /// Recursively perform peephole optimization, until the result stops
    /// changing (i.e. there is nothing more we can optimize).
    let rec optimizeRec (text: List<TextStmt>): List<TextStmt> =
        /// Optimized assembly code
        let optText = optimizeText text
        if (optText = text) then text
                            else optimizeRec optText
    asm.SetText (optimizeRec asm.GetText)
