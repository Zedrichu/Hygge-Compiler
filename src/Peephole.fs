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

/// Compute log2 of a positive power of 2.
/// NOTE: only valid for n that are positive powers of 2 (i.e. isPositivePowerOfTwo n = true).
let private log2 (n: int32) : uint32 =
    uint32 (System.Numerics.BitOperations.Log2(uint32 n))

/// Optimize a list of Text segment statements.
/// Many pattern-matching cases for different optimization methods are organized and
/// ordered based on 4 core principles:
/// 1. Specific identities before general reductions (special constants, identity & zero)
/// 2. Larger instruction windows before smaller windows.
/// 3. Memory & arithmetic simplification before redundant move elimination.
/// 4. Strict directionality (never reverse transformations, commutative swapping rules)
/// Peephole optimization must form a strictly acyclic, terminating rewriting system (avoid infinite loops).
let internal optimizeText (text: List<TextStmt>): List<TextStmt> =
    /// Canonical Tail-Recursivity implementation for compiler Tail Call Optimization (TCO)
    let rec loop (acc: List<TextStmt>) (remaining: List<TextStmt>): List<TextStmt> =
        match remaining with
        // _____________________Optimization Tier 1_______________________
        // Multi-instruction Control Flow Patterns (3-instruction window)
        // _______________________________________________________________

        // --- Inverting Conditional Branches over Unconditional Jumps
        // BEQ/BEQZ over J to immediate label -> BNE/BEQZ
        | (RV.BEQ(rs1, rs2, target1), comment1) :: (RV.J(target2), _) ::
          (RV.LABEL(label), comment3) :: rest when label = target1 ->
            let inst1 = (RV.BNE(rs1, rs2, target2), $"{comment1} (inverted branch over jump)")
            let inst2 = (RV.LABEL(label), comment3)
            loop (inst2 :: inst1 :: acc) rest
        | (RV.BEQZ(rs1, target1), comment1) :: (RV.J(target2), _) ::
          (RV.LABEL(label), comment3) :: rest when label = target1 ->
            let inst1 = (RV.BNEZ(rs1, target2), $"{comment1} (inverted branch over jump)")
            let inst2 = (RV.LABEL(label), comment3)
            loop (inst2 :: inst1 :: acc) rest
        // BNE/BNEZ over J to immediate label -> BEQ/BEQZ
        | (RV.BNE(rs1, rs2, target1), comment1) :: (RV.J(target2), _) ::
          (RV.LABEL(label), comment3) :: rest when label = target1 ->
            let inst1 = (RV.BEQ(rs1, rs2, target2), $"{comment1} (inverted branch over jump)")
            let inst2 = (RV.LABEL(label), comment3)
            loop (inst2 :: inst1 :: acc) rest
        | (RV.BNEZ(rs1, target1), comment1) :: (RV.J(target2), _) ::
          (RV.LABEL(label), comment3) :: rest when label = target1 ->
            let inst1 = (RV.BEQZ(rs1, target2), $"{comment1} (inverted branch over jump)")
            let inst2 = (RV.LABEL(label), comment3)
            loop (inst2 :: inst1 :: acc) rest
        // BNE/BNEZ over JR to immediate label -> BEQ/BEQZ
        | (RV.BNEZ(rs1, target1), comment1) :: (RV.LA(rAddr, target2), _) ::
          (RV.JR(rJump), _) :: (RV.LABEL(label), comment3) ::
          rest when label = target1 && rAddr = rJump ->
            let inst1 = (RV.BEQZ(rs1, target2), $"{comment1} (inverted branch over JR)")
            let inst2 = (RV.LABEL(label), comment3)
            loop (inst2 :: inst1 :: acc) rest

        // ________________________Optimization Tier 2__________________________
        // Redundant Branching & Control Flow Fallthrough (2-instruction window)
        // _____________________________________________________________________

        // --- Canonicalized Fold of Address Load + Register Jump to Direct Jump
        | (RV.LA(r1, target), _) :: (RV.JR(r2), comment) :: rest when r1 = r2 ->
            let inst = (RV.J(target), comment)
            loop (inst :: acc) rest

        // --- Branch / Jump to the Immediately Following Label
        // Eliminate unconditional jump to the next line (labeled instruction)
        | (RV.J(label1), _) :: (RV.LABEL(label2), comment) :: rest when label1 = label2 ->
            let inst = (RV.LABEL(label1), comment)
            loop (inst :: acc) rest

        // Eliminate conditional branches jumping to the next line (labeled instruction)
        | (RV.BEQ(_, _, label1), _) :: (RV.LABEL(label2), comment) :: rest when label1 = label2 ->
            let inst = (RV.LABEL(label1), comment)
            loop (inst :: acc) rest
        | (RV.BNE(_, _, label1), _) :: (RV.LABEL(label2), comment) :: rest when label1 = label2 ->
            let inst = (RV.LABEL(label1), comment)
            loop (inst :: acc) rest
        | (RV.BEQZ(_, label1), _) :: (RV.LABEL(label2), comment) :: rest when label1 = label2 ->
            let inst = (RV.LABEL(label1), comment)
            loop (inst :: acc) rest
        | (RV.BNEZ(_, label1), _) :: (RV.LABEL(label2), comment) :: rest when label1 = label2 ->
            let inst = (RV.LABEL(label1), comment)
            loop (inst :: acc) rest

        // ________________________Optimization Tier 3________________________________
        // Memory / Stack Optimizations (store-forwarding, reload elimination, fusion)
        // ___________________________________________________________________________

        // --- Store-forwarding / Reload Elimination
        | (RV.SW(rs0, imm1, rs1), comment) :: (RV.LW(rd, imm2, rs2), comment1) ::
          rest when imm1.Value = imm2.Value && rs1 = rs2 ->
            let newAcc =
              if rs0 = rd then // forward store
                let inst = (RV.SW(rs0, imm1, rs1), comment)
                inst :: acc
              else // eliminate reload
                let inst1 = (RV.SW(rs0, imm1, rs1), comment)
                let inst2 = (RV.MV(rd, rs0), comment1)
                inst2 :: inst1 :: acc
            loop newAcc rest


        // --- Stack Pointer Adjustment Fusion and Cancellation
        | (RV.ADDI(rd1, rs1, imm1), comment1) :: (RV.ADDI(rd2, rs2, imm2), comment2) ::
          rest when rd1 = rs1 && rd1 = Reg.sp && rd2 = rs2 && rd2 = Reg.sp ->
            let newValue = imm1.Value + imm2.Value
            let potentialStatements =
                match newValue with
                | 0 -> [] // Cancellation
                | x when isImm12 x -> // Fusion
                    [RV.ADDI(rd1, rs1, Imm12(x)), $"{comment1} {comment2}"]
                | _ -> // Cannot fuse — emit both unchanged
                    [RV.ADDI(rd1, rs1, imm1), comment1; RV.ADDI(rd2, rs2, imm2), comment2]
            loop (potentialStatements @ acc) rest

        // ________________________Optimization Tier 4a_________________________
        // Algebraic Zero & Unit Identities (special cases: *1, /1, *0, +0, -0)
        // _____________________________________________________________________

        // --- Algebraic Identity: Adding / Subtracting Zero
        | (RV.ADDI(rd, rs, imm), comment) :: rest when imm.Value = 0 ->
            let newAcc =
                if rd = rs then acc
                else (RV.MV(rd, rs), comment) :: acc
            loop newAcc rest
        | (RV.ADD(rd, rs1, rs2), comment) :: rest when rs2 = Reg.zero ->
            let newAcc =
                if rd = rs1 then acc
                else (RV.MV(rd, rs1), comment) :: acc
            loop newAcc rest
        | (RV.ADD(rd, rs1, rs2), comment) :: rest when rs1 = Reg.zero ->
            let newAcc =
                if rd = rs2 then acc
                else (RV.MV(rd, rs2), comment) :: acc
            loop newAcc rest
        | (RV.SUB(rd, rs1, rs2), comment) :: rest when rs2 = Reg.zero ->
            let newAcc =
                if rd = rs1 then acc
                else (RV.MV(rd, rs1), comment) :: acc
            loop newAcc rest

        // ________________________Optimization Tier 4b_______________________________
        // Logical Identities, Absorbers & Bitwise Canonicalization (Zero / All-Ones)
        // ___________________________________________________________________________

        // --- AND/ANDI: Absorbers, register-register identities and bitmask identity
        // AND with zero register → move zero (zero absorbs AND)
        | (RV.AND(rd, _, rs2), comment) :: rest when rs2 = Reg.zero ->
            let inst = (RV.MV(rd, Reg.zero), $"{comment} (AND absorber: & zero = 0)")
            loop (inst :: acc ) rest
        | (RV.AND(rd, rs1, _), comment) :: rest when rs1 = Reg.zero ->
            let inst = (RV.MV(rd, Reg.zero), $"{comment} (AND absorber: zero & = 0)")
            loop (inst :: acc) rest
        // AND with self → move (or no-op if same register)
        | (RV.AND(rd, rs1, rs2), comment) :: rest when rs1 = rs2 ->
            let newAcc =
                if rd = rs1 then acc
                else (RV.MV(rd, rs1), $"{comment} (AND self-idempotent: x & x = x)") :: acc
            loop newAcc rest
        // ANDI with 0 → move zero (immediate zero absorbs AND)
        | (RV.ANDI(rd, _, imm), comment) :: rest when imm.Value = 0 ->
            let inst = (RV.MV(rd, Reg.zero), $"{comment} (ANDI absorber: & 0 = 0)")
            loop (inst :: acc ) rest
        // ANDI with -1 identity (all-ones, 2's complement signed) -> MV (or no-op if same register)
        | (RV.ANDI(rd, rs, imm), comment) :: rest when imm.Value = -1 ->
            let newAcc =
                if rd = rs then acc
                else (RV.MV(rd, rs), $"{comment} (ANDI bitmask identity: & 11...111 = self)") :: acc
            loop newAcc rest

        // --- OR/ORI: Absorbers, register-register identities and bitmask identity
        // OR with zero register → move (zero is identity for OR)
        | (RV.OR(rd, rs1, rs2), comment) :: rest when rs2 = Reg.zero ->
            let inst = (RV.MV(rd, rs1), $"{comment} (OR identity: | zero = self)")
            loop (inst :: acc) rest
        | (RV.OR(rd, rs1, rs2), comment) :: rest when rs1 = Reg.zero ->
            let inst = (RV.MV(rd, rs2), $"{comment} (OR identity: zero | = self)")
            loop (inst :: acc) rest
        // OR with self → move (idempotent)
        | (RV.OR(rd, rs1, rs2), comment) :: rest when rs1 = rs2 ->
            let newAcc =
                if rd = rs1 then acc
                else (RV.MV(rd, rs1), $"{comment} (OR self-idempotent: x | x = x)") :: acc
            loop newAcc rest
        // ORI with all-ones → load -1 (all-ones bitmask absorbs OR, 2's complement signed)
        | (RV.ORI(rd, _, imm), comment) :: rest when imm.Value = -1 ->
            let inst = (RV.LI(rd, -1), $"{comment} (ORI absorber: | 11...11 = 11...11)")
            loop (inst :: acc) rest
        // ORI with zero (identity) -> MV (or no-op if same register)
        | (RV.ORI(rd, rs, imm), comment) :: rest when imm.Value = 0 ->
            let newAcc =
                if rd = rs then acc
                else (RV.MV(rd, rs), $"{comment} (ORI identity: | 0 = self)") :: acc
            loop newAcc rest

        // --- XOR: Canonical forms and simplifications
        // XOR with 0 → move (zero is identity for XOR)
        | (RV.XOR(rd, rs1, rs2), comment) :: rest when rs2 = Reg.zero ->
            let newAcc =
                if rd = rs1 then acc
                else (RV.MV(rd, rs1), $"{comment} (XOR identity: ^ zero = self)") :: acc
            loop newAcc rest
        | (RV.XOR(rd, rs1, rs2), comment) :: rest when rs1 = Reg.zero ->
            let newAcc =
                if rd = rs2 then acc
                else (RV.MV(rd, rs2), $"{comment} (XOR identity: ^ zero = self)") :: acc
            loop newAcc rest
        // XORI with 0 → move (zero is identity for XOR)
        | (RV.XORI(rd, rs, imm), comment) :: rest when imm.Value = 0 ->
            let newAcc =
                if rd = rs then acc
                else (RV.MV(rd, rs), $"{comment} (XORI identity: ^ 0 = self)") :: acc
            loop newAcc rest
        // XORI with -1 (all-ones) → NOT (bitwise complement)
        | (RV.XORI(rd, rs, imm), comment) :: rest when imm.Value = -1 ->
            let inst = (RV.NOT(rd, rs), $"{comment} (XORI -1 = NOT)")
            loop (inst :: acc) rest

        // Double NOT cancellation → move (or no-op)
        | (RV.NOT(rd1, rs), _) ::
          (RV.NOT(rd2, rt), comment2) :: rest when rd1 = rt ->
            let newAcc =
                if rd2 = rs then acc
                else (RV.MV(rd2, rs), $"{comment2} (double NOT = identity)") :: acc
            loop newAcc rest

        // --- Shifts: Identity and absorber simplifications
        // Shift by 0 → move (or no-op) — shift by zero is identity
        | (RV.SLLI(rd, rs, shamt), comment) :: rest when shamt.Value = 0u ->
            let newAcc =
                if rd = rs then acc
                else (RV.MV(rd, rs), $"{comment} (SLLI 0 = identity)") :: acc
            loop newAcc rest
        | (RV.SRLI(rd, rs, shamt), comment) :: rest when shamt.Value = 0u ->
            let newAcc =
                if rd = rs then acc
                else (RV.MV(rd, rs), $"{comment} (SRLI 0 = identity)") :: acc
            loop newAcc rest
        | (RV.SRAI(rd, rs, shamt), comment) :: rest when shamt.Value = 0u ->
            let newAcc =
                if rd = rs then acc
                else (RV.MV(rd, rs), $"{comment} (SRAI 0 = identity)") :: acc
            loop newAcc rest

        // Shift of zero register → move zero (shifting zero always yields zero)
        | (RV.SLLI(rd, rs, _), comment) :: rest when rs = Reg.zero ->
            let inst = (RV.MV(rd, Reg.zero), $"{comment} (SLLI zero reg = 0)")
            loop (inst :: acc) rest
        | (RV.SRLI(rd, rs, _), comment) :: rest when rs = Reg.zero ->
            let inst = (RV.MV(rd, Reg.zero), $"{comment} (SRLI zero reg = 0)")
            loop (inst :: acc) rest
        | (RV.SRAI(rd, rs, _), comment) :: rest when rs = Reg.zero ->
            let inst = (RV.MV(rd, Reg.zero), $"{comment} (SRAI zero reg = 0)")
            loop (inst :: acc) rest

        // --- Algebraic Identity: Multiplying / Dividing Identity & Zero
        // Multiplication by 1 (identity) -> result is the other register
        | (RV.LI(rd1, 1), comment1) :: (RV.MUL(rd2, rs1, rs2), comment2) :: rest when rd1 = rs2 ->
            let inst1 = (RV.LI(rd1, 1), comment1)
            let inst2 = (RV.MV(rd2, rs1), $"{comment2} (reduced * 1)")
            loop (inst2 :: inst1 :: acc) rest
        | (RV.LI(rd1, 1), comment1) :: (RV.MUL(rd2, rs1, rs2), comment2) :: rest when rd1 = rs1 ->
            let inst1 = (RV.LI(rd1, 1), comment1)
            let inst2 = (RV.MV(rd2, rs2), $"{comment2} (reduced * 1)")
            loop (inst2 :: inst1 :: acc ) rest

        // Multiplication by 0 (zero) -> result is null
        | (RV.LI(rd1, 0), comment1) :: (RV.MUL(rd2, rs1, rs2), comment2)
            :: rest when rd1 = rs2 || rd1 = rs1 ->
            let inst1 = (RV.LI(rd1, 0), comment1)
            let inst2 = (RV.MV(rd2, Reg.zero), $"{comment2} (reduced * 0)")
            loop (inst2 :: inst1 :: acc) rest

        // Division by 1 (identity) -> result is the dividend register
        | (RV.LI(rd1, 1), comment1) :: (RV.DIV(rd2, rs1, rs2), comment2) :: rest when rd1 = rs2 ->
            let inst1 = (RV.LI(rd1, 1), comment1)
            let inst2 = (RV.MV(rd2, rs1), $"{comment2} (reduced / 1)")
            loop (inst2 :: inst1 :: acc) rest

        // ________________________Optimization Tier 5__________________________________
        // General Strength Reduction & Immediate Folding (shifts, immediate arithmetic)
        // _____________________________________________________________________________

        // --- General Strength Reduction for Arbitrary Powers of 2 (2^k)
        // Multiplication by any 2^k ->> shift logical left by k
        | (RV.LI(rd1, value), comment1) :: (RV.MUL(rd2, rs1, rs2), comment2)
          :: rest when (rs1 = rd1 || rs2 = rd1) && isPositivePowerOfTwo value && value > 1 ->
            let other_reg = if rs1 = rd1 then rs2 else rs1
            let k_shift = log2 value
            let inst1 = (RV.LI(rd1, value), comment1)
            let inst2 = (RV.SLLI(rd2, other_reg, Shamt(k_shift)), $"{comment2} (strength reduction << {k_shift})")
            loop (inst2 :: inst1 :: acc) rest

        // Division by any 2^k ->> shift arithmetic right by k
        | (RV.LI(rd1, value), comment1) ::
          (RV.DIV(rd2, rs1, rs2), comment2) ::
          rest when rd1 = rs2 && isPositivePowerOfTwo value && value > 1 ->
            let k_shift = log2 value
            let inst1 = (RV.LI(rd1, value), comment1)
            let inst2 = (RV.SRAI(rd2, rs1, Shamt(k_shift)), $"{comment2} (strength reduction >> {k_shift})")
            loop (inst2 :: inst1 :: acc) rest

        // // Specific Strength Reduction
        // | (RV.LI(rd1, value), comment1) :: (RV.MUL(rd2, rs1, rs2), comment2) :: rest
        //     when value = 2 && rd1 = rs2 ->
        //     (RV.LI(rd1, value), comment1) :: (RV.SLLI(rd2, rs1, Shamt(1u)), comment2) :: optimizeText rest
        // | (RV.LI(rd1, value), comment1) :: (RV.DIV(rd2, rs1, rs2), comment2) :: rest
        //     when value = 64 && rd1 = rs2 ->
        //     (RV.LI(rd1, value), comment1) :: (RV.SRAI(rd2, rs1, Shamt(6u)), comment2) :: optimizeText rest

        // --- Immediate Addition Folding
        | (RV.LI(rd1, value), comment1) :: (RV.ADD(rd2, rs1, rs2), comment2)
          :: rest when rd1 = rs2 && (isImm12 value) ->
            let inst1 = (RV.LI(rd1, value), comment1)
            let inst2 = (RV.ADDI(rd2, rs1, Imm12(value)), comment2)
            loop (inst2 :: inst1 :: acc) rest

        // ____________________Optimization Tier 5b______________________________
        // Logical Immediate Folding (LI + logical-op -> logical-op-immediate)
        // Canonical direction only (immediate register is the right operand),
        // to preserve strict directionality and prevent termination hazards.
        // ______________________________________________________________________

        // LI + OR -> ORI (fold constant into OR instruction)
        | (RV.LI(rd1, value), comment1) :: (RV.OR(rd2, rs1, rs2), comment2)
          :: rest when rd1 = rs2 && rd1 <> rs1 && isImm12 value ->
            let inst1 = (RV.LI(rd1, value), comment1)
            let inst2 = (RV.ORI(rd2, rs1, Imm12(value)), $"{comment2} (OR immediate folding)")
            loop (inst2 :: inst1 :: acc) rest

        // LI + AND -> ANDI (fold constant into AND instruction)
        | (RV.LI(rd1, value), comment1) :: (RV.AND(rd2, rs1, rs2), comment2)
          :: rest when rd1 = rs2 && rd1 <> rs1 && isImm12 value ->
            let inst1 = (RV.LI(rd1, value), comment1)
            let inst2 = (RV.ANDI(rd2, rs1, Imm12(value)), $"{comment2} (AND immediate folding)")
            loop (inst2 :: inst1 :: acc) rest

        // LI + XOR -> XORI (fold constant into XOR instruction)
        | (RV.LI(rd1, value), comment1) :: (RV.XOR(rd2, rs1, rs2), comment2)
          :: rest when rd1 = rs2 && rd1 <> rs1 && isImm12 value ->
            let inst1 = (RV.LI(rd1, value), comment1)
            let inst2 = (RV.XORI(rd2, rs1, Imm12(value)), $"{comment2} (XOR immediate folding)")
            loop (inst2 :: inst1 :: acc) rest

        // _____________________Optimization Tier 6_______________________
        // Redundant Assignments, Duplicate Instructions & No-Op Cleanups
        // _______________________________________________________________

        // --- Dead Store Elimination (Consecutive Stores to Same Address)
        | (RV.SW(_, imm1, rp1), _) :: (RV.SW(rs2, imm2, rp2), comment2)
          :: rest when imm1.Value = imm2.Value && rp1 = rp2 ->
            let inst = (RV.SW(rs2, imm2, rp2), comment2)
            loop (inst :: acc) rest

        // -- Redundant Assignment Elimination
        // Duplicate immediate load removal
        | (RV.LI(rd1, _), _) :: (RV.LI(rd2, imm2), comment2) :: rest when rd1 = rd2 ->
            let inst = (RV.LI(rd2, imm2), comment2)
            loop (inst :: acc) rest

        // Duplicate move removal
        | (RV.MV(rd1, rs1), comment1) :: (RV.MV(rd2, rs2), _) :: rest when rd1 = rd2 && rs1 = rs2 ->
            let inst = (RV.MV(rd1, rs1), comment1)
            loop (inst :: acc) rest

        // Cross-move simplification
        | (RV.MV(rd1, rs1), comment1) :: (RV.MV(rd2, rs2), comment2)
          :: rest when rd1 = rs2 && rd2 = rs1 ->
            let inst = (RV.MV(rd1, rd2), $"{comment1} {comment2}")
            loop (inst :: acc) rest

        // Overwritten-move removal
        | (RV.MV(rd1, rs1), comment1) :: (RV.LI(rd2, value), comment2)
          :: rest when rd1 = rd2 && (isImm12 value) ->
            let inst = (RV.LI(rd1, value), $"{comment1} {comment2}")
            loop (inst :: acc) rest

        // --- Self-Subtraction & Self-XOR (Yield Loaded Zero)
        | (RV.SUB(rd, rs1, rs2), comment) :: rest when rs1 = rs2 ->
            let inst = (RV.LI(rd, 0), $"{comment} (self-sub zero)")
            loop (inst :: acc) rest
        | (RV.XOR(rd, rs1, rs2), comment) :: rest when rs1 = rs2 ->
            let inst = (RV.MV(rd, Reg.zero), $"{comment} (self-xor zero)")
            loop (inst :: acc) rest

        // --- Self-move Elimination
        | (RV.MV(rd, rs), comment) :: rest when rd = rs -> loop acc rest

        // TIER 7: Default Fallthrough
        | stmt :: rest ->
            // If we are here, we did not find any pattern to optimize: we skip the
            // first assembly statement and try with the rest
            loop (stmt :: acc) rest

        | [] -> List.rev acc
    // Trigger one full optimization loop over the ASM text (chain of statements).
    loop [] text

/// Optimize the given assembly code.
let optimize (asm: Asm): Asm =
    let maxPasses = 5 // Round fuel
    Log.info "Starting peephole optimization"
    /// Recursively perform peephole optimization, until the result stops
    /// changing (i.e. there is nothing more we can optimize, optimization fixed-point).
    let rec optimizeRec (pass: int) (text: List<TextStmt>): List<TextStmt> =
        if pass > maxPasses then
            failwith $"Peephole optimization cycle detected: exceeded {maxPasses} passes without converging."
        /// Optimized assembly code
        let optText = optimizeText text
        if (optText = text) then text
                            else optimizeRec (pass + 1) optText // Aim for fixed-point

    let optAsm = optimizeRec 1 asm.GetText
    let rawCount = asm.GetText |> List.length
    let optCount = optAsm |> List.length
    let reduction = rawCount - optCount
    let pct = if rawCount > 0 then (float reduction / float rawCount) * 100.0 else 0.0
    Log.info $"Peephole optimization complete: {rawCount} → {optCount} instructions (reduced by {reduction}, {pct:F1}%%)"
    printf $"Peephole optimization complete: {rawCount} → {optCount} instructions (reduced by {reduction}, {pct:F1}%%)"
    asm.SetText optAsm
