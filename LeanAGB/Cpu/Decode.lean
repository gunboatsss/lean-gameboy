/-
  LeanAGB.Cpu.Decode — complete ARMv4T Thumb decoder (ARM stub).
  Every v4T Thumb encoding maps to a real constructor; only genuinely
  unpredictable/UNDEFINED space (v5 BLX prefix, Bcond-AL, SUBS-reg is
  covered) and non-v4T forms → .nop (never locks up, mirrors DMG
  invalid-opcode policy). Field layout follows ARM ARM DDI 0100I.
-/
import LeanAGB.Basic

namespace AGB

/-- Full ARMv4T Thumb instruction set (GAS names in comments). -/
inductive ThumbInstr where
  | movsImm (rd : Nat) (imm : Nat) : ThumbInstr
  | cmpImm (rn : Nat) (imm : Nat) : ThumbInstr
  | addImm (rd : Nat) (imm : Nat) : ThumbInstr
  | subImm (rd : Nat) (imm : Nat) : ThumbInstr
  | addsImm (rd rn : Nat) (imm : Nat) : ThumbInstr
  | subsImm (rd rn : Nat) (imm : Nat) : ThumbInstr
  | addsReg (rd rn rm : Nat) : ThumbInstr
  | subsReg (rd rn rm : Nat) : ThumbInstr
  | lslImm (rd rm : Nat) (sh : Nat) : ThumbInstr
  | lsrImm (rd rm : Nat) (sh : Nat) : ThumbInstr
  | asrImm (rd rm : Nat) (sh : Nat) : ThumbInstr
  | alu2 (op rs rd : Nat) : ThumbInstr
  | mul (rs rd : Nat) : ThumbInstr
  | hiAdd (rs rd : Nat) : ThumbInstr
  | hiCmp (rs rd : Nat) : ThumbInstr
  | hiMov (rs rd : Nat) : ThumbInstr
  | strReg (rd rn rm : Nat) : ThumbInstr
  | ldrReg (rd rn rm : Nat) : ThumbInstr
  | strbReg (rd rn rm : Nat) : ThumbInstr
  | ldrbReg (rd rn rm : Nat) : ThumbInstr
  | strhReg (rd rn rm : Nat) : ThumbInstr
  | ldrhReg (rd rn rm : Nat) : ThumbInstr
  | ldsbReg (rd rn rm : Nat) : ThumbInstr
  | ldshReg (rd rn rm : Nat) : ThumbInstr
  | strImm (rd rn : Nat) (off : Nat) : ThumbInstr
  | ldrImm (rd rn : Nat) (off : Nat) : ThumbInstr
  | strbImm (rd rn : Nat) (off : Nat) : ThumbInstr
  | ldrbImm (rd rn : Nat) (off : Nat) : ThumbInstr
  | strhImm (rd rn : Nat) (off : Nat) : ThumbInstr
  | ldrhImm (rd rn : Nat) (off : Nat) : ThumbInstr
  | strSp (rd : Nat) (off : Nat) : ThumbInstr
  | ldrSp (rd : Nat) (off : Nat) : ThumbInstr
  | adrPc (rd : Nat) (off : Nat) : ThumbInstr
  | adrSp (rd : Nat) (off : Nat) : ThumbInstr
  | addSp (off : Int) : ThumbInstr
  | push (lr : Bool) (mask : Nat) : ThumbInstr
  | pop (pc : Bool) (mask : Nat) : ThumbInstr
  | stm (rb : Nat) (mask : Nat) : ThumbInstr
  | ldm (rb : Nat) (mask : Nat) : ThumbInstr
  | bcond (cond : Nat) (off : Int) : ThumbInstr
  | b (off : Int) : ThumbInstr
  | blPre (off : Int) : ThumbInstr
  | blSuf (off : Int) : ThumbInstr
  | bx (rm : Nat) : ThumbInstr
  | swi (imm : Nat) : ThumbInstr
  | ldrLit (rd : Nat) (off : Nat) : ThumbInstr
  | nop : ThumbInstr
deriving DecidableEq, Repr

/-- Sign-extend an 11-bit Thumb branch offset (already ×1; caller scales). -/
def sx11 (raw : Nat) : Int :=
  if raw < 0x400 then (raw : Int) else ((raw : Int) - 0x800)

/-- Decode one 16-bit Thumb halfword. Branch order = encoding priority
    (SWI before Bcond so 0xDFxx is always SWI, never Bcond-NV). -/
def decodeThumb (hw : UInt16) : ThumbInstr :=
  let v := hw.toNat
  if v >>> 11 == 0b00100 then
    .movsImm ((v >>> 8) &&& 0x7) (v &&& 0xFF)
  else if v >>> 11 == 0b00101 then
    .cmpImm ((v >>> 8) &&& 0x7) (v &&& 0xFF)
  else if v >>> 11 == 0b00110 then
    .addImm ((v >>> 8) &&& 0x7) (v &&& 0xFF)
  else if v >>> 11 == 0b00111 then
    .subImm ((v >>> 8) &&& 0x7) (v &&& 0xFF)
  else if v >>> 11 == 0b00011 then
    -- bit 10 selects register (0) vs immediate (1); bit 9 ADD (0)/SUB (1)
    if (v >>> 10) &&& 0x1 == 0 then
      if (v >>> 9) &&& 0x1 == 0 then
        .addsReg (v &&& 0x7) ((v >>> 3) &&& 0x7) ((v >>> 6) &&& 0x7)
      else
        .subsReg (v &&& 0x7) ((v >>> 3) &&& 0x7) ((v >>> 6) &&& 0x7)
    else
      if (v >>> 9) &&& 0x1 == 0 then
        .addsImm (v &&& 0x7) ((v >>> 3) &&& 0x7) ((v >>> 6) &&& 0x7)
      else
        .subsImm (v &&& 0x7) ((v >>> 3) &&& 0x7) ((v >>> 6) &&& 0x7)
  else if v >>> 11 == 0b00000 then
    -- LSL (immediate): 00000 sh(5) rm(3) rd(3); sh = 0 is identity
    .lslImm (v &&& 0x7) ((v >>> 3) &&& 0x7) ((v >>> 6) &&& 0x1F)
  else if v >>> 11 == 0b00001 then
    -- LSR: imm5 = 0 means shift 32
    let sh := (v >>> 6) &&& 0x1F
    .lsrImm (v &&& 0x7) ((v >>> 3) &&& 0x7) (if sh == 0 then 32 else sh)
  else if v >>> 11 == 0b00010 then
    -- ASR: imm5 = 0 means shift 32
    let sh := (v >>> 6) &&& 0x1F
    .asrImm (v &&& 0x7) ((v >>> 3) &&& 0x7) (if sh == 0 then 32 else sh)
  else if v >>> 10 == 0b010000 then
    -- ALU two-operand: op = bits 9-6; MUL (13) gets its own constructor
    let op := (v >>> 6) &&& 0xF
    let rs := (v >>> 3) &&& 0x7
    let rd := v &&& 0x7
    if op == 13 then .mul rs rd else .alu2 op rs rd
  else if v >>> 10 == 0b010001 then
    -- Hi-register ops: Op = bits 9-8; H1 = bit 7, H2 = bit 6
    let op := (v >>> 8) &&& 0x3
    let rs := ((v >>> 3) &&& 0x7) + (if ((v >>> 6) &&& 0x1 == 1) then 8 else 0)
    let rd := (v &&& 0x7) + (if ((v >>> 7) &&& 0x1 == 1) then 8 else 0)
    if op == 0 then .hiAdd rs rd
    else if op == 1 then .hiCmp rs rd
    else if op == 2 then .hiMov rs rd
    -- Op=3 with H1=0 (bits 11-7 = 01110) is BX; H1=1 is v5 BLX-reg → nop
    else if (v >>> 7) &&& 0x1F == 0b01110 then .bx ((v >>> 3) &&& 0xF)
    else .nop  -- v5 BLX-register form: UNDEFINED on v4T
  else if v >>> 12 == 0b0101 then
    -- Register-offset loads/stores; bit 9 selects word/byte (0) vs H/SB/SH (1)
    let ro := (v >>> 6) &&& 0x7
    let rb := (v >>> 3) &&& 0x7
    let rd := v &&& 0x7
    if (v >>> 9) &&& 0x1 == 0 then
      let l := (v >>> 11) &&& 0x1
      let b := (v >>> 10) &&& 0x1
      if l == 0 && b == 0 then .strReg rd rb ro
      else if l == 0 then .strbReg rd rb ro
      else if b == 0 then .ldrReg rd rb ro
      else .ldrbReg rd rb ro
    else
      let h := (v >>> 11) &&& 0x1
      let s := (v >>> 10) &&& 0x1
      if h == 0 && s == 0 then .strhReg rd rb ro
      else if h == 0 then .ldsbReg rd rb ro
      else if s == 0 then .ldrhReg rd rb ro
      else .ldshReg rd rb ro
  else if v >>> 11 == 0b01100 then
    .strImm (v &&& 0x7) ((v >>> 3) &&& 0x7) (((v >>> 6) &&& 0x1F) * 4)
  else if v >>> 11 == 0b01101 then
    .ldrImm (v &&& 0x7) ((v >>> 3) &&& 0x7) (((v >>> 6) &&& 0x1F) * 4)
  else if v >>> 11 == 0b01110 then
    .strbImm (v &&& 0x7) ((v >>> 3) &&& 0x7) ((v >>> 6) &&& 0x1F)
  else if v >>> 11 == 0b01111 then
    .ldrbImm (v &&& 0x7) ((v >>> 3) &&& 0x7) ((v >>> 6) &&& 0x1F)
  else if v >>> 11 == 0b01001 then
    -- LDR (literal, PC-relative): addr = ((PC+4)&~3)+imm8*4
    .ldrLit ((v >>> 8) &&& 0x7) ((v &&& 0xFF) * 4)
  else if v >>> 11 == 0b10000 then
    .strhImm (v &&& 0x7) ((v >>> 3) &&& 0x7) (((v >>> 6) &&& 0x1F) * 2)
  else if v >>> 11 == 0b10001 then
    .ldrhImm (v &&& 0x7) ((v >>> 3) &&& 0x7) (((v >>> 6) &&& 0x1F) * 2)
  else if v >>> 11 == 0b10010 then
    .strSp ((v >>> 8) &&& 0x7) ((v &&& 0xFF) * 4)
  else if v >>> 11 == 0b10011 then
    .ldrSp ((v >>> 8) &&& 0x7) ((v &&& 0xFF) * 4)
  else if v >>> 11 == 0b10100 then
    .adrPc ((v >>> 8) &&& 0x7) ((v &&& 0xFF) * 4)
  else if v >>> 11 == 0b10101 then
    .adrSp ((v >>> 8) &&& 0x7) ((v &&& 0xFF) * 4)
  else if v >>> 12 == 0b1011 then
    if (v >>> 8) &&& 0xF == 0b0000 then
      -- ADD SP, #±imm7*4 (bit 7 = sign)
      let mag := ((v &&& 0x7F) * 4 : Nat)
      .addSp (if ((v >>> 7) &&& 0x1 == 1) then -((mag : Int)) else (mag : Int))
    else if v >>> 9 == 0b1011010 then
      .push (((v >>> 8) &&& 0x1) == 1) (v &&& 0xFF)
    else if v >>> 9 == 0b1011110 then
      .pop (((v >>> 8) &&& 0x1) == 1) (v &&& 0xFF)
    else .nop
  else if v >>> 11 == 0b11000 || v >>> 11 == 0b11001 then
    -- STMIA (L=0) / LDMIA (L=1), always writeback in Thumb
    if (v >>> 11) &&& 0x1 == 0 then .stm ((v >>> 8) &&& 0x7) (v &&& 0xFF)
    else .ldm ((v >>> 8) &&& 0x7) (v &&& 0xFF)
  else if v >>> 8 == 0b11011111 then
    .swi (v &&& 0xFF)
  else if v >>> 12 == 0b1101 then
    -- Bcond; cond 1110 (AL) is UNDEFINED, 1111 already taken by SWI above
    let cond := (v >>> 8) &&& 0xF
    if cond == 0b1110 then .nop
    else
      let raw := v &&& 0xFF
      let s := if raw < 0x80 then (raw : Int) * 2 else ((raw : Int) - 0x100) * 2
      .bcond cond s
  else if v >>> 11 == 0b11100 then
    -- B (unconditional); +4 pipeline handled in exec
    .b (sx11 (v &&& 0x7FF) * 2)
  else if v >>> 11 == 0b11110 then
    -- BL prefix: LR = PC+4+(off11<<12)
    .blPre (sx11 (v &&& 0x7FF) * 4096)
  else if v >>> 11 == 0b11111 then
    -- BL suffix: target = LR+(off11<<1). The low part is UNSIGNED
    -- (only the prefix carries the sign); sign-extending it here
    -- misroutes every BL whose low half is ≥ 0x400 (found via luvdis).
    .blSuf (((v &&& 0x7FF) * 2 : Nat) : Int)
  else .nop
  -- note: 0b11101 (v5 BLX prefix) and 010001/11 non-BX fall here → .nop

/-- Full ARMv4T ARM instruction set (no coprocessors on GBA: CDP/MCR/MRC
    and the v5 BLX forms decode to .nop; TST/TEQ/CMP/CMN require S). -/
inductive ArmInstr where
  | dpImm (cond op s rn rd : Nat) (rot imm8 : Nat) : ArmInstr
  | dpReg (cond op s rn rd rm : Nat) (shTy : Nat) (shReg : Bool) (sa : Nat) : ArmInstr
  | mul (cond : Nat) (acc s : Bool) (rd rn rm rs : Nat) : ArmInstr
  | mull (cond : Nat) (u acc s : Bool) (rdHi rdLo rm rs : Nat) : ArmInstr
  | mrs (cond : Nat) (psr rd : Nat) : ArmInstr
  | msrImm (cond : Nat) (psr : Nat) (mask rot imm8 : Nat) : ArmInstr
  | msrReg (cond : Nat) (psr : Nat) (mask rm : Nat) : ArmInstr
  | memImm (cond : Nat) (p u b w l : Bool) (rn rd : Nat) (off12 : Nat) : ArmInstr
  | memReg (cond : Nat) (p u b w l : Bool) (rn rd rm : Nat) (shTy amt5 : Nat) : ArmInstr
  | memH (cond : Nat) (p u w l : Bool) (h s : Bool) (rn rd : Nat) (isImm : Bool) (off : Nat) : ArmInstr
  | ldmStm (cond : Nat) (p u s w l : Bool) (rn : Nat) (mask : Nat) : ArmInstr
  | b (cond : Nat) (off : Int) : ArmInstr
  | bl (cond : Nat) (off : Int) : ArmInstr
  | bx (cond : Nat) (rm : Nat) : ArmInstr
  | swi (cond : Nat) (imm : Nat) : ArmInstr
  | swp (cond : Nat) (b : Bool) (rn rd rm : Nat) : ArmInstr
  | nop : ArmInstr
deriving DecidableEq, Repr

/-- Sign-extend a 24-bit branch offset (caller scales by 4). -/
def sx24 (raw : Nat) : Int :=
  if raw < 0x800000 then (raw : Int) else ((raw : Int) - 0x1000000)

/-- ARM DataProc fallthrough (MRS/MSR/SWP/memH claimed above).
    TST/TEQ/CMP/CMN require S (v4T: S=0 there is UNDEFINED → `.nop`). -/
def decodeArmDp (v cond : Nat) : ArmInstr :=
  let op := (v >>> 21) &&& 0xF
  let s := (v >>> 20) &&& 0x1
  if (op == 8 || op == 9 || op == 10 || op == 11) && s == 0 then .nop
  else if (v >>> 25) &&& 0x1 == 1 then
    .dpImm cond op s ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF)
      ((v >>> 8) &&& 0xF) (v &&& 0xFF)
  else
    let rm := v &&& 0xF
    let shTy := (v >>> 5) &&& 0x3
    if ((v >>> 4) &&& 0x1) == 1 then
      .dpReg cond op s ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF)
        rm shTy true ((v >>> 8) &&& 0xF)
    else
      let amt5 := (v >>> 7) &&& 0x1F
      .dpReg cond op s ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF)
        rm shTy false
        (if (shTy == 1 || shTy == 2) && amt5 == 0 then 32 else amt5)

/-- Decode one 32-bit ARM word. Order follows the ARM ARM decode tree
    (multiply-misc before DataProc fallthrough; SWI in the 11-group). -/
def decodeArm (w : UInt32) : ArmInstr :=
  let v := w.toNat
  let cond := v >>> 28
  if (v >>> 26) &&& 0x3 == 0b00 then
    if (v >>> 4) &&& 0xF == 0b1001 && (v >>> 22) &&& 0x3F == 0 then
      -- MUL/MLA: bits 27-22 = 000000 (result = Rm*Rs [+ Rn])
      .mul cond (((v >>> 21) &&& 0x1) == 1) (((v >>> 20) &&& 0x1) == 1)
        ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF) (v &&& 0xF) ((v >>> 8) &&& 0xF)
    else if (v >>> 4) &&& 0xF == 0b1001 && (v >>> 23) &&& 0x1F == 0b00001 then
      -- MULL: bits 27-23 = 00001 (64-bit result)
      .mull cond (((v >>> 22) &&& 0x1) == 1) (((v >>> 21) &&& 0x1) == 1)
        (((v >>> 20) &&& 0x1) == 1)
        ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF) (v &&& 0xF) ((v >>> 8) &&& 0xF)
    else if (v >>> 4) &&& 0xFFFFFF == 0x12FFF1 then
      .bx cond (v &&& 0xF)
    else if (v >>> 23) &&& 0x1F == 0b00010 then
      -- 00010 group: memH nibbles (B/D/F) route before SWP/MRS/MSR
      -- (e.g. STRH with P=1,U=0 also lands in 00010). Valid unless
      -- S=1,H=0,L=0 (no such transfer; SWP lives in another nibble).
      if (v >>> 4) &&& 0xF == 0xB || (v >>> 4) &&& 0xF == 0xD
          || (v >>> 4) &&& 0xF == 0xF then
        let h := ((v >>> 5) &&& 0x1) == 1
        let s := ((v >>> 6) &&& 0x1) == 1
        let l := ((v >>> 20) &&& 0x1) == 1
        if s && !h && !l then .nop
        else
          .memH cond (((v >>> 24) &&& 0x1) == 1) (((v >>> 23) &&& 0x1) == 1)
            (((v >>> 21) &&& 0x1) == 1) l
            h s ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF)
            (((v >>> 22) &&& 0x1) == 1)
            (if ((v >>> 22) &&& 0x1) == 1 then
              (((v >>> 8) &&& 0xF) * 16 + (v &&& 0xF)) else (v &&& 0xF))
      else if (v >>> 20) &&& 0x3 == 0b00 && (v >>> 4) &&& 0xFFF == 0x009 then
        .swp cond (((v >>> 22) &&& 0x1) == 1)
          ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF) (v &&& 0xF)
      else if (v >>> 16) &&& 0x3F == 0b001111 && (v &&& 0xFFF) == 0 then
        -- MRS: bits 21-16 = 001111, bits 11-0 SBZ (keeps TST r15,rn
        -- with zero low bits from misrouting; residual is UNPREDICTABLE)
        .mrs cond ((v >>> 22) &&& 0x1) ((v >>> 12) &&& 0xF)
      else if (v >>> 20) &&& 0x3 == 0b10 && (v >>> 4) &&& 0xFF == 0
          && (v >>> 12) &&& 0xF == 0xF then
        -- MSR-reg: bits 21-20 = 10, bits 15-4 required
        -- (1111_00000000 per the encoding table)
        let psr := (v >>> 22) &&& 0x1
        let mask := (v >>> 16) &&& 0xF
        if (v >>> 25) &&& 0x1 == 1 then .nop  -- (defensive; unreachable)
        else .msrReg cond psr mask (v &&& 0xF)
      -- Not MRS/MSR/SWP: register-form DataProc also matches bits
      -- 27-23 = 00010 when op ∈ {TST,TEQ,CMP,CMN} (bit24=1,bit23=0),
      -- so fall through to DataProc instead of `.nop` (the BIOS-boot
      -- hang: `cmp lr, fp` decoded as nop, flags never set).
      else decodeArmDp v cond
    else if ((v >>> 20) &&& 0xFF == 0x32 || (v >>> 20) &&& 0xFF == 0x36)
        && (v >>> 12) &&& 0xF == 0xF
        && !(((v >>> 22) &&& 0x1) == 0 && ((v >>> 16) &&& 0xF) == 0) then
      -- MSR-immediate: bits 27-20 = 0011001R, bits 15-12 required 1111;
      -- R=0 with empty mask is not MSR (falls to DataProc, nopped as
      -- TST-S0 there). Bit 25 = 1, so it never reaches the group above.
      .msrImm cond ((v >>> 22) &&& 0x1) ((v >>> 16) &&& 0xF)
        ((v >>> 8) &&& 0xF) (v &&& 0xFF)
    else if ((v >>> 4) &&& 0xF == 0xB || (v >>> 4) &&& 0xF == 0xD
        || (v >>> 4) &&& 0xF == 0xF) && (v >>> 25) &&& 0x7 == 0b000 then
      -- halfword / signed-byte transfers (bits 27-25 = 000);
      -- S=1,H=0 needs L=1 (LDRSB), else UNDEFINED
      let h := ((v >>> 5) &&& 0x1) == 1
      let s := ((v >>> 6) &&& 0x1) == 1
      let l := ((v >>> 20) &&& 0x1) == 1
      if s && !h && !l then .nop
      else
        .memH cond (((v >>> 24) &&& 0x1) == 1) (((v >>> 23) &&& 0x1) == 1)
          (((v >>> 21) &&& 0x1) == 1) (((v >>> 20) &&& 0x1) == 1)
          h s ((v >>> 16) &&& 0xF) ((v >>> 12) &&& 0xF)
          (((v >>> 22) &&& 0x1) == 1)
          (if ((v >>> 22) &&& 0x1) == 1 then
            (((v >>> 8) &&& 0xF) * 16 + (v &&& 0xF)) else (v &&& 0xF))
    else decodeArmDp v cond
  else if (v >>> 26) &&& 0x3 == 0b01 then
    let p := ((v >>> 24) &&& 0x1) == 1
    let u := ((v >>> 23) &&& 0x1) == 1
    let b := ((v >>> 22) &&& 0x1) == 1
    let ww := ((v >>> 21) &&& 0x1) == 1
    let l := ((v >>> 20) &&& 0x1) == 1
    let rn := (v >>> 16) &&& 0xF
    let rd := (v >>> 12) &&& 0xF
    if (v >>> 25) &&& 0x1 == 0 then
      .memImm cond p u b ww l rn rd (v &&& 0xFFF)
    else if ((v >>> 4) &&& 0x1) == 1 then .nop  -- reg-shift offset: UNPREDICTABLE
    else
      let shTy := (v >>> 5) &&& 0x3
      let amt5 := (v >>> 7) &&& 0x1F
      .memReg cond p u b ww l rn rd (v &&& 0xF) shTy
        (if (shTy == 1 || shTy == 2) && amt5 == 0 then 32 else amt5)
  else if (v >>> 26) &&& 0x3 == 0b10 then
    if (v >>> 25) &&& 0x1 == 1 then
      -- B/BL (v4T: no BLX; H-bit space decodes as BL)
      let s := sx24 (v &&& 0xFFFFFF) * 4
      if ((v >>> 24) &&& 0x1) == 1 then .bl cond s else .b cond s
    else
      .ldmStm cond (((v >>> 24) &&& 0x1) == 1) (((v >>> 23) &&& 0x1) == 1)
        (((v >>> 22) &&& 0x1) == 1) (((v >>> 21) &&& 0x1) == 1)
        (((v >>> 20) &&& 0x1) == 1) ((v >>> 16) &&& 0xF) (v &&& 0xFFFF)
  else
    if (v >>> 24) &&& 0xF == 0b1111 then .swi cond (v &&& 0xFFFFFF)
    else .nop  -- coprocessors: none on GBA

end AGB
