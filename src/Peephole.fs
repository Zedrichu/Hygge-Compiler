// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Functions to perform peephole optimizations on RISC-V assembly code.
module Peephole

open RISCV

/// Check if an integer is a positive power of 2
let private isPositivePowerOfTwo (n: int32) : bool =
    n > 0 && (n &&& (n - 1)) = 0

/// Compute log2 of a positive power of 2
let private log2 (n: int32) : uint32 =
    uint32 (System.Numerics.BitOperations.Log2(uint32 n))

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

    // Self-move Elimination
    | (RV.MV(rd, rs), comment) :: rest when rd = rs ->
        optimizeText rest

    // Store-forwarding / Reload Elimination
    | (RV.SW(rs0, imm1, rs1), comment) ::
      (RV.LW(rd, imm2, rs2), comment1) ::
      rest when imm1 = imm2 && rs1 = rs2 ->
        if rs0 = rd then
            (RV.SW(rs0, imm1, rs1), comment) :: optimizeText rest
        else (RV.SW(rs0, imm1, rs1), comment) ::
                    (RV.MV(rd, rs0), comment1) :: optimizeText rest

    // Stack Pointer Adjustment Fusion and Cancellation
    | (RV.ADDI(rd1, rs1, imm1), comment1) ::
      (RV.ADDI(rd2, rs2, imm2), comment2) ::
      rest when rd1 = rs1 && rd1 = Reg.sp &&
                 rd2 = rs2 && rd2 = Reg.sp ->
        let newValue = imm1.Value + imm2.Value
        let potentialStatements =
            match newValue with
            | 0 -> [] // Cancellation
            | x when isImm12 x -> // Fusion
                [RV.ADDI(rd1, rs1, Imm12(x)), $"{comment1} {comment2}"]
        potentialStatements @ optimizeText rest

    // Algebraic Identity: Adding / Subtracting Zero
    | (RV.ADDI(rd, rs, imm), comment) :: rest when imm.Value = 0 ->
        if rd = rs then optimizeText rest
        else (RV.MV(rd, rs), comment) :: optimizeText rest
    | (RV.ADD(rd, rs1, rs2), comment) :: rest when rs2 = Reg.zero ->
        if rd = rs1 then optimizeText rest
        else (RV.MV(rd, rs1), comment) :: optimizeText rest
    | (RV.ADD(rd, rs1, rs2), comment) :: rest when rs1 = Reg.zero ->
        if rd = rs2 then optimizeText rest
        else (RV.MV(rd, rs2), comment) :: optimizeText rest
    | (RV.SUB(rd, rs1, rs2), comment) :: rest when rs2 = Reg.zero ->
        if rd = rs1 then optimizeText rest
        else (RV.MV(rd, rs1), comment) :: optimizeText rest
    
    // Algebraic Identity: Multiplying / Dividing Identity & Zero
    // Multiplication by 1 (identity) -> result is the other register
    | (RV.LI(rd1, 1), comment1) ::
      (RV.MUL(rd2, rs1, rs2), comment2) ::
      rest when rd1 = rs2 ->
        (RV.LI(rd1, 1), comment1) ::
        (RV.MV(rd2, rs1), $"{comment2} (reduced * 1)") :: optimizeText rest
    | (RV.LI(rd1, 1), comment1) ::
      (RV.MUL(rd2, rs1, rs2), comment2) ::
      rest when rd1 = rs1 ->
        (RV.LI(rd1, 1), comment1) ::
        (RV.MV(rd2, rs2), $"{comment2} (reduced * 1)") :: optimizeText rest

    // Multiplication by 0 (zero) -> result is null
    | (RV.LI(rd1, 0), comment1) ::
      (RV.MUL(rd2, rs1, rs2), comment2) ::
      rest when rd1 = rs2 || rd1 = rs1 ->
        (RV.LI(rd1, 0), comment1) ::
        (RV.MV(rd2, Reg.zero), $"{comment2} (reduced * 0)") :: optimizeText rest

    // Division by 1 (identity) -> result is the dividend register
    | (RV.LI(rd1, 1), comment1) ::
      (RV.DIV(rd2, rs1, rs2), comment2) ::
      rest when rd1 = rs2 ->
        (RV.LI(rd1, 1), comment1) ::
        (RV.MV(rd2, rs1), $"{comment2} (reduced / 1)") :: optimizeText rest

    // Branch / Jump to the Immediately Following Label

    // Inverting Conditional Branches over Unconditional Jumps

    // Boolean Comparison & Branch Fusion

    // Dead Store Elimination (Consecutive Stores to Same Address)

    // Self-Substraction & Self-XOR (Yield Loaded Zero)

    // General Strength Reduction for Arbitrary Powers of 2 (2^k)
    | (RV.LI(rd1, value), comment1) ::
      (RV.MUL(rd2, rs1, rs2), comment2) ::
      rest when (rs1 = rd1 || rs2 = rd1) && isPositivePowerOfTwo value ->
        let other_reg = if rs1 = rd1 then rs2 else rs1
        let k_shift = log2 value
        (RV.LI(rd1, value), comment1) ::
        (RV.SLLI(rd2, other_reg, Shamt(k_shift)), $"{comment2} (strength reduction << {k_shift})") ::
        optimizeText rest

    | (RV.LI(rd1, value), comment1) ::
      (RV.DIV(rd2, rs1, rs2), comment2) ::
      rest when rd1 = rs2 && isPositivePowerOfTwo value ->
        let k_shift = log2 value
        (RV.LI(rd1, value), comment1) ::
        (RV.SRAI(rd2, rs1, Shamt(k_shift)), $"{comment2} (strength reduction >> {k_shift})") ::
        optimizeText rest

    // // Specific Strength Reduction
    // | (RV.LI(rd1, value), comment1) :: (RV.MUL(rd2, rs1, rs2), comment2) :: rest
    //     when value = 2 && rd1 = rs2 ->
    //     (RV.LI(rd1, value), comment1) :: (RV.SLLI(rd2, rs1, Shamt(1u)), comment2) :: optimizeText rest
    // | (RV.LI(rd1, value), comment1) :: (RV.DIV(rd2, rs1, rs2), comment2) :: rest
    //     when value = 64 && rd1 = rs2 ->
    //     (RV.LI(rd1, value), comment1) :: (RV.SRAI(rd2, rs1, Shamt(6u)), comment2) :: optimizeText rest

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
