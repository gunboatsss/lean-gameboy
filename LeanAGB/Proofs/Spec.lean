/-
  LeanAGB.Proofs.Spec — ARM-ARM-traced execution vectors.
  Convention: every execution-vector theorem cites the operation it pins
  from the ARM Architecture Reference Manual (DDI 0100I, Thumb
  instruction set). Each is a closed `decide` over `execThumb`, so the
  kernel replays the exact documented semantics on every build.
  (There is no Sail model of ARMv4T; the machine-checked HOL4/L3 model
  of Fox et al. covers this ISA but lives in another prover. These
  vectors are our Lean-native spec traceability.)
-/
import LeanAGB.Bus

namespace AGB

/-- Concrete test state: 16 GPRs + CPSR + 16-byte EWRAM window. -/
def specState (rs : Array UInt32) (cpsr : UInt32) (mem : ByteArray) : AGBState :=
  { ({} : AGBState) with regs := { r := rs, cpsr := cpsr }, ewram := mem }

def zero16 : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- ADC (add with carry): 0xFFFFFFFF + 1 + C(1) = 1, carry out. -/
def specAdc : AGBState :=
  specState #[0xFFFFFFFF, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x2000003F zero16

theorem spec_adc_value :
    (execThumb specAdc (.alu2 5 1 0)).1.regs.get 0 = 1 := by
  decide

theorem spec_adc_carry :
    cpsrC (execThumb specAdc (.alu2 5 1 0)).1.regs.cpsr = true := by
  decide

/-- ADC signed overflow: 0x7FFFFFFF + 1 = 0x80000000, V set. -/
def specAdcV : AGBState :=
  specState #[0x7FFFFFFF, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_adc_overflow :
    cpsrV (execThumb specAdcV (.alu2 5 1 0)).1.regs.cpsr = true := by
  decide

/-- SBC (subtract with carry): 0 - 1 - NOT-C(0) = 0xFFFFFFFF, no carry. -/
def specSbc : AGBState :=
  specState #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x2000003F zero16

theorem spec_sbc_value :
    (execThumb specSbc (.alu2 7 1 0)).1.regs.get 0 = 0xFFFFFFFF := by
  decide

theorem spec_sbc_borrow :
    cpsrC (execThumb specSbc (.alu2 7 1 0)).1.regs.cpsr = false := by
  decide

/-- MUL: 6 * 7 = 42, flags clean. -/
def specMul : AGBState :=
  specState #[0, 0, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_mul_value :
    (execThumb specMul (.mul 3 2)).1.regs.get 2 = 42 := by
  decide

/-- ROR by register: ROR(0x80000001, 1) = 0xC0000000, C = ex-bit 0. -/
def specRor : AGBState :=
  specState #[0x80000001, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_ror_value :
    (execThumb specRor (.alu2 6 1 0)).1.regs.get 0 = 0xC0000000 := by
  decide

theorem spec_ror_carry :
    cpsrC (execThumb specRor (.alu2 6 1 0)).1.regs.cpsr = true := by
  decide

/-- LSL #0 is identity and preserves carry. -/
def specLsl0 : AGBState :=
  specState #[0x12345678, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x2000003F zero16

theorem spec_lsl0_carry_kept :
    cpsrC (execThumb specLsl0 (.lslImm 0 0 0)).1.regs.cpsr = true := by
  decide

/-- LSR #32 (encoded imm5 = 0): result 0, C = old bit 31. -/
def specLsr32 : AGBState :=
  specState #[0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_lsr32_value :
    (execThumb specLsr32 (.lsrImm 0 0 32)).1.regs.get 0 = 0 := by
  decide

theorem spec_lsr32_carry :
    cpsrC (execThumb specLsr32 (.lsrImm 0 0 32)).1.regs.cpsr = true := by
  decide

/-- PUSH {r0,r1} then POP {r2,r3}: round trip + SP restored. -/
def specStack : AGBState :=
  specState #[0xDEAD, 0xBEEF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x02000010, 0, 0] 0x3F zero16

theorem spec_push_pop_lo :
    (execThumb (execThumb specStack (.push false 3)).1 (.pop false 0x0C)).1.regs.get 2
      = 0xDEAD := by
  decide

theorem spec_push_pop_hi :
    (execThumb (execThumb specStack (.push false 3)).1 (.pop false 0x0C)).1.regs.get 3
      = 0xBEEF := by
  decide

theorem spec_push_pop_sp :
    (execThumb (execThumb specStack (.push false 3)).1 (.pop false 0x0C)).1.regs.get 13
      = 0x02000010 := by
  decide

/-- STM r5!,{r0,r1} then LDM r6,{r2,r3}: values + writeback. -/
def specBlock : AGBState :=
  specState #[0xAAAA, 0xBBBB, 0, 0, 0, 0x02000000, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F
    zero16

theorem spec_stm_ldm_lo :
    (execThumb (execThumb specBlock (.stm 5 0x03)).1 (.ldm 6 0x0C)).1.regs.get 2
      = 0xAAAA := by
  decide

theorem spec_stm_ldm_hi :
    (execThumb (execThumb specBlock (.stm 5 0x03)).1 (.ldm 6 0x0C)).1.regs.get 3
      = 0xBBBB := by
  decide

theorem spec_stm_writeback :
    (execThumb specBlock (.stm 5 0x03)).1.regs.get 5 = 0x02000008 := by
  decide

theorem spec_ldm_writeback :
    (execThumb (execThumb specBlock (.stm 5 0x03)).1 (.ldm 6 0x0C)).1.regs.get 6
      = 0x02000008 := by
  decide

/-- Bcond taken (EQ, Z = 1): PC stays on the -4 loop. -/
def specTaken : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x4000003F zero16

theorem spec_bcond_taken :
    (execThumb specTaken (.bcond 0 (-4))).1.regs.pc = 0x08000000 := by
  decide

/-- Bcond not taken (EQ, Z = 0): PC falls through. -/
def specNotTaken : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x3F zero16

theorem spec_bcond_nottaken :
    (execThumb specNotTaken (.bcond 0 (-4))).1.regs.pc = 0x08000002 := by
  decide

/-- BL pair: prefix sets LR, suffix jumps and sets return|1. -/
def specBl : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x3F zero16

theorem spec_bl_target :
    (execThumb (execThumb specBl (.blPre 0)).1 (.blSuf 0x10)).1.regs.pc = 0x08000014 := by
  decide

theorem spec_bl_return :
    (execThumb (execThumb specBl (.blPre 0)).1 (.blSuf 0x10)).1.regs.get 14
      = 0x08000005 := by
  decide

/-- BL pair with a negative prefix intermediate (BIOS `bl 0x82E` from
    0x8B0: LR = 0x8B4 - 0x1000 wraps, suffix adds back to the target).
    `Int.toNat` truncation put LR = 0 here and misrouted every far
    backward BL issued from low BIOS addresses (the boot reboot loop). -/
def specBlBios : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x8B0] 0x3F zero16

theorem spec_bl_neg_target :
    (execThumb (execThumb specBlBios (.blPre (-4096))).1 (.blSuf 3962)).1.regs.pc
      = 0x82E := by
  decide

/-- Register CMP sets Z on equal operands (the Huff-boot hang companion:
    `cmp lr, fp` left Z stale, so the output word never fired). -/
def specCmpReg : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 8, 0x1000] 0x1F zero16

theorem spec_cmpReg_z :
    (execArm specCmpReg (.dpReg 14 10 1 14 0 11 0 false 0)).1.regs.cpsr
      = 0x6000001F := by
  decide

/-- LDSB sign-extends 0xFF to 0xFFFFFFFF. -/
def specLdsb : AGBState :=
  specState #[0, 0, 0, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F
    (ByteArray.mk #[0xFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

theorem spec_ldsb_sign :
    (execThumb specLdsb (.ldsbReg 0 3 0)).1.regs.get 0 = 0xFFFFFFFF := by
  decide

/-- MOV PC (hi): target aligned down, Thumb state kept. -/
def specHiPc : AGBState :=
  specState #[0x08000011, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_himov_pc :
    (execThumb specHiPc (.hiMov 0 15)).1.regs.pc = 0x08000010 := by
  decide

theorem spec_himov_thumb :
    cpsrT (execThumb specHiPc (.hiMov 0 15)).1.regs.cpsr = true := by
  decide

/-- ADD Rd,#imm wraps: 0xFFFFFFFF + 1 = 0 with C and Z. -/
def specAddWrap : AGBState :=
  specState #[0, 0, 0xFFFFFFFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_add_wrap_value :
    (execThumb specAddWrap (.addImm 2 1)).1.regs.get 2 = 0 := by
  decide

theorem spec_add_wrap_carry :
    cpsrC (execThumb specAddWrap (.addImm 2 1)).1.regs.cpsr = true := by
  decide

/-- CMP writes no register but sets Z on equality. -/
def specCmp : AGBState :=
  specState #[5, 0xDEAD, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_cmp_flag :
    cpsrZ (execThumb specCmp (.cmpImm 0 5)).1.regs.cpsr = true := by
  decide

theorem spec_cmp_nowrite :
    (execThumb specCmp (.cmpImm 0 5)).1.regs.get 1 = 0xDEAD := by
  decide

/-- NEG: 0 - 1 = 0xFFFFFFFF. -/
def specNeg : AGBState :=
  specState #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_neg_value :
    (execThumb specNeg (.alu2 9 1 0)).1.regs.get 0 = 0xFFFFFFFF := by
  decide

/-- ADR (PC): word-aligned PC+4 plus scaled offset. -/
def specAdr : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x3F zero16

theorem spec_adr_value :
    (execThumb specAdr (.adrPc 0 16)).1.regs.get 0 = 0x08000014 := by
  decide

/-- STRB/LDRB round trip through the EWRAM window. -/
def specByteMem : AGBState :=
  specState #[0x12345678, 0, 0, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_strb_ldrb :
    (execThumb (execThumb specByteMem (.strbImm 0 3 1)).1 (.ldrbImm 1 3 1)).1.regs.get 1
      = 0x78 := by
  decide

/-- STRH/LDRH round trip (low halfword stored). -/
def specHalfMem : AGBState :=
  specState #[0xABCD, 0, 0, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F zero16

theorem spec_strh_ldrh :
    (execThumb (execThumb specHalfMem (.strhImm 0 3 2)).1 (.ldrhImm 1 3 2)).1.regs.get 1
      = 0xABCD := by
  decide

/-- LDRB zero-extends (complement to the LDSB sign vector above). -/
def specLdrbZ : AGBState :=
  specState #[0, 0, 0, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x3F
    (ByteArray.mk #[0xFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

theorem spec_ldrb_zeroext :
    (execThumb specLdrbZ (.ldrbImm 1 3 0)).1.regs.get 1 = 0xFF := by
  decide

/-- ADD SP, #-8 then #+8: modular stack pointer arithmetic. -/
def specSp : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x02000010, 0, 0] 0x3F zero16

theorem spec_addsp_down :
    (execThumb specSp (.addSp (-8))).1.regs.get 13 = 0x02000008 := by
  decide

theorem spec_addsp_up :
    (execThumb (execThumb specSp (.addSp (-8))).1 (.addSp 8)).1.regs.get 13
      = 0x02000010 := by
  decide

/-- ADR (SP): Rd = SP + scaled offset. -/
def specAdrSp : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x02000000, 0, 0] 0x3F zero16

theorem spec_adrsp_value :
    (execThumb specAdrSp (.adrSp 0 64)).1.regs.get 0 = 0x02000040 := by
  decide

/-- STM/LDM with empty list: PC stored, base advances 0x40, PC reloaded. -/
def specEmptyBlock : AGBState :=
  specState
    #[0, 0, 0, 0, 0, 0x02000000, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x3F
    zero16

theorem spec_stm_empty_store :
    memRead32 (execThumb specEmptyBlock (.stm 5 0)).1 0x02000000 = 0x08000000 := by
  decide

theorem spec_stm_empty_advance :
    (execThumb specEmptyBlock (.stm 5 0)).1.regs.get 5 = 0x02000040 := by
  decide

theorem spec_ldm_empty_pc :
    (execThumb (execThumb specEmptyBlock (.stm 5 0)).1 (.ldm 6 0)).1.regs.pc
      = 0x08000000 := by
  decide

/-- POP {PC} follows bit 0 into ARM state when clear. -/
def specPopArm : AGBState :=
  specState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x02000000, 0, 0] 0x3F
    (ByteArray.mk #[0x10, 0x00, 0x00, 0x08, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

theorem spec_pop_pc_value :
    (execThumb specPopArm (.pop true 0)).1.regs.pc = 0x08000010 := by
  decide

theorem spec_pop_pc_arm :
    cpsrT (execThumb specPopArm (.pop true 0)).1.regs.cpsr = false := by
  decide

/-- PUSH {LR} then POP {PC}: call/return round trip through the stack. -/
def specCallRet : AGBState :=
  specState
    #[0x11111111, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x02000010, 0x08000005, 0] 0x3F
    zero16

theorem spec_callret_pc :
    (execThumb (execThumb specCallRet (.push true 0)).1 (.pop true 0)).1.regs.pc
      = 0x08000004 := by
  decide

theorem spec_callret_sp :
    (execThumb (execThumb specCallRet (.push true 0)).1 (.pop true 0)).1.regs.get 13
      = 0x02000010 := by
  decide

theorem spec_callret_thumb :
    cpsrT (execThumb (execThumb specCallRet (.push true 0)).1 (.pop true 0)).1.regs.cpsr
      = true := by
  decide

-- ── Phase B: ARM execution vectors (ARM ARM DDI 0100I, ARM ISA) ──
-- ARM state helper: SYS/ARM CPSR, PC installed. -/
def armState (rs : Array UInt32) (pc : UInt32) : AGBState :=
  { ({} : AGBState) with regs := { r := rs.set! 15 pc, cpsr := 0x1F }, ewram := zero16 }

/-- ARM state with explicit CPSR (flag-sensitive vectors). -/
def armStateC (rs : Array UInt32) (cpsr pc : UInt32) : AGBState :=
  { ({} : AGBState) with regs := { r := rs.set! 15 pc, cpsr := cpsr }, ewram := zero16 }

/-- ADD r1,r0,#imm with PC-relative read: PC reads +8 in ARM state. -/
theorem spec_arm_pc_read :
    (execArm (armState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.dpImm 14 4 0 15 0 0 0)).1.regs.get 0 = 0x08000008 := by
  decide

/-- SUBS sets Z and C on exact equality. -/
theorem spec_arm_subs_zero :
    (execArm (armState #[5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.dpImm 14 2 1 0 0 0 5)).1.regs.get 0 = 0 := by
  decide

theorem spec_arm_subs_z :
    cpsrZ (execArm (armState #[5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.dpImm 14 2 1 0 0 0 5)).1.regs.cpsr = true := by
  decide

/-- MUL then MLA accumulate: 6*7 = 42, 42+100 = 142. -/
theorem spec_arm_mul :
    (execArm (armState #[0, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.mul 14 false false 0 0 1 2)).1.regs.get 0 = 42 := by
  decide

theorem spec_arm_mla :
    (execArm (armState #[0, 6, 7, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.mul 14 true false 0 3 1 2)).1.regs.get 0 = 142 := by
  decide

/-- UMULL 64-bit: 0xFFFFFFFF² = 0xFFFFFFFE00000001. -/
theorem spec_arm_umull_hi :
    (execArm (armState #[0xFFFFFFFF, 0xFFFFFFFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.mull 14 true false false 3 2 0 1)).1.regs.get 3 = 0xFFFFFFFE := by
  decide

theorem spec_arm_umull_lo :
    (execArm (armState #[0xFFFFFFFF, 0xFFFFFFFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.mull 14 true false false 3 2 0 1)).1.regs.get 2 = 1 := by
  decide

/-- SMULL signed: (-1) * 2 = -2, N set. -/
theorem spec_arm_smull_hi :
    (execArm (armState #[0xFFFFFFFF, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.mull 14 false false true 3 2 0 1)).1.regs.get 3 = 0xFFFFFFFF := by
  decide

theorem spec_arm_smull_lo :
    (execArm (armState #[0xFFFFFFFF, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.mull 14 false false true 3 2 0 1)).1.regs.get 2 = 0xFFFFFFFE := by
  decide

theorem spec_arm_smull_n :
    cpsrN (execArm (armState #[0xFFFFFFFF, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.mull 14 false false true 3 2 0 1)).1.regs.cpsr = true := by
  decide

/-- MRS reads CPSR; MSR/MRS round trip installs Z. -/
theorem spec_arm_mrs :
    (execArm (armStateC #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0xA000001F 0x08000000)
      (.mrs 14 0 0)).1.regs.get 0 = 0xA000001F := by
  decide

theorem spec_arm_msr_mrs :
    (execArm (execArm (armState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x1F)
      (.msrImm 14 0 8 1 1)).1 (.mrs 14 0 1)).1.regs.get 1 = 0x4000001F := by
  decide

/-- ARM LDR/STR word round trip. -/
theorem spec_arm_ldr_str :
    (execArm (execArm (armState #[0xDEADBEEF, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.memImm 14 true true false false false 1 0 0)).1
      (.memImm 14 true true false false true 1 2 0)).1.regs.get 2 = 0xDEADBEEF := by
  decide

/-- ARM state with explicit EWRAM window (for PC-relative tests). -/
def armMemState (rs : Array UInt32) (pc : UInt32) (mem : ByteArray) : AGBState :=
  { ({} : AGBState) with regs := { r := rs.set! 15 pc, cpsr := 0x1F }, ewram := mem }

/-- LDR with Rn=15 reads PC+8 (ARM pipeline; the Kirby boot killer). -/
theorem spec_arm_ldrpc_value :
    (execArm (armMemState
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x02000000
      (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0xEF, 0xBE, 0xAD, 0xDE, 0, 0, 0, 0]))
      (.memImm 14 true true false false true 15 2 0)).1.regs.get 2
      = 0xDEADBEEF := by
  decide

/-- ARM STMIA/LDMIA block round trip with writeback. -/
theorem spec_arm_block_lo :
    (execArm (execArm (armState #[0x02000000, 0x11111111, 0x22222222, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.ldmStm 14 false true false true false 0 0x06)).1
      (.ldmStm 14 false true false true true 3 0x18)).1.regs.get 3 = 0x11111111 := by
  decide

theorem spec_arm_block_hi :
    (execArm (execArm (armState #[0x02000000, 0x11111111, 0x22222222, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.ldmStm 14 false true false true false 0 0x06)).1
      (.ldmStm 14 false true false true true 3 0x18)).1.regs.get 4 = 0x22222222 := by
  decide

theorem spec_arm_block_wb :
    (execArm (armState #[0x02000000, 0x11111111, 0x22222222, 0x02000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.ldmStm 14 false true false true false 0 0x06)).1.regs.get 0 = 0x02000008 := by
  decide

/-- STMDB stores descending from base-4 with matching writeback. -/
theorem spec_arm_stmdb_wb :
    (execArm (armState #[0x02000008, 0x11111111, 0x22222222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.ldmStm 14 true false false true false 0 0x06)).1.regs.get 0 = 0x02000000 := by
  decide

theorem spec_arm_stmdb_lo :
    memRead32
      (execArm (armState #[0x02000008, 0x11111111, 0x22222222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
        (.ldmStm 14 true false false true false 0 0x06)).1 0x02000000 = 0x11111111 := by
  decide

theorem spec_arm_stmdb_hi :
    memRead32
      (execArm (armState #[0x02000008, 0x11111111, 0x22222222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
        (.ldmStm 14 true false false true false 0 0x06)).1 0x02000004 = 0x22222222 := by
  decide

/-- SWP exchanges register and memory. -/
theorem spec_arm_swp_reg :
    (execArm (armState #[0x02000000, 0xBBBBBBBB, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.swp 14 false 0 2 1)).1.regs.get 2 = 0 := by
  decide

theorem spec_arm_swp_mem :
    memRead32
      (execArm (armState #[0x02000000, 0xBBBBBBBB, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
        (.swp 14 false 0 2 1)).1 0x02000000 = 0xBBBBBBBB := by
  decide

/-- RRX through carry: ROR#0 with C=1 prefixes bit 31. -/
theorem spec_arm_rrx :
    (execArm (armStateC #[0, 0x80000001, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0x2000001F 0x08000000)
      (.dpReg 14 13 0 0 0 1 3 false 0)).1.regs.get 0 = 0xC0000000 := by
  decide

/-- ARM B taken (AL) and skipped (NV). -/
theorem spec_arm_b_taken :
    (execArm (armState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.b 14 8)).1.regs.pc = 0x08000010 := by
  decide

theorem spec_arm_b_nv :
    (execArm (armState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.b 15 8)).1.regs.pc = 0x08000004 := by
  decide

/-- ARM BL sets LR = PC+4 and jumps PC+8+off. -/
theorem spec_arm_bl :
    (execArm (armState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.bl 14 8)).1.regs.get 14 = 0x08000004 := by
  decide

theorem spec_arm_bl_target :
    (execArm (armState #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000] 0x08000000)
      (.bl 14 8)).1.regs.pc = 0x08000010 := by
  decide

/-- MOVS PC restores SPSR (exception-return shape), following its T. -/
def specArmRet : AGBState :=
  { ({} : AGBState) with
    regs := { r := #[0x08000011, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x08000000],
              cpsr := 0x13, spsr_svc := 0x400000B3 } }

theorem spec_arm_movs_pc :
    (execArm specArmRet (.dpReg 14 13 1 0 15 0 0 false 0)).1.regs.pc = 0x08000010 := by
  decide

theorem spec_arm_movs_cpsr :
    (execArm specArmRet (.dpReg 14 13 1 0 15 0 0 false 0)).1.regs.cpsr = 0x400000B3 := by
  decide

end AGB
