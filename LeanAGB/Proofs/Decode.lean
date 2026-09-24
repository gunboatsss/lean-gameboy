/-
  LeanAGB.Proofs.Decode — decoder contracts for the full ARMv4T Thumb set:
  spot vectors per class, exhaustive per-class sweeps (no `.nop` in any
  valid encoding), and v4T-scope pins (v5/UNDEFINED space stays `.nop`).
-/
import LeanAGB.Cpu.Decode
import LeanAGB.Bios

namespace AGB

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem decode_movs_r0 : decodeThumb 0x2045 = .movsImm 0 0x45 := by decide

theorem decode_adds_reg : decodeThumb 0x1881 = .addsReg 1 0 2 := by decide

theorem decode_adds_r2 : decodeThumb 0x1842 = .addsReg 2 0 1 := by decide

theorem decode_b_loop : decodeThumb 0xE7FE = .b (-4) := by decide

/-- Bool-guard falsity from a Nat disequation (feeds `if_neg`). -/
theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : ((a == b) = false) := by
  simp [h]

/-- Bool-guard truth from a Nat equation (feeds `if_pos`). -/
theorem beq_true_of_eq {a b : Nat} (h : a = b) : ((a == b) = true) := by
  simp [h]

/-- Every unconditional-`B` halfword decodes with the exact `sx11` offset
    (fast-step dispatch mirrors this class). -/
theorem decodeThumb_b_eq (hw : UInt16) (h11 : hw.toNat >>> 11 = 28) :
    decodeThumb hw = .b (sx11 (hw.toNat &&& 0x7FF) * 2) := by
  have f11 : ∀ k : Nat, hw.toNat >>> 11 ≠ k → ((hw.toNat >>> 11 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have f10 : ∀ k : Nat, hw.toNat >>> 10 ≠ k → ((hw.toNat >>> 10 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have f12 : ∀ k : Nat, hw.toNat >>> 12 ≠ k → ((hw.toNat >>> 12 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have f9 : ∀ k : Nat, hw.toNat >>> 9 ≠ k → ((hw.toNat >>> 9 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have f8 : ∀ k : Nat, hw.toNat >>> 8 ≠ k → ((hw.toNat >>> 8 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have tB : ((hw.toNat >>> 11 == 28) = true) := beq_true_of_eq h11
  simp [decodeThumb, h11, tB,
    f11 4 (by omega), f11 5 (by omega), f11 6 (by omega), f11 7 (by omega),
    f11 3 (by omega), f11 0 (by omega), f11 1 (by omega), f11 2 (by omega),
    f10 16 (by omega), f10 17 (by omega),
    f12 5 (by omega),
    f11 12 (by omega), f11 13 (by omega), f11 14 (by omega),
    f11 15 (by omega), f11 9 (by omega),
    f11 16 (by omega), f11 17 (by omega), f11 18 (by omega),
    f11 19 (by omega), f11 20 (by omega), f11 21 (by omega),
    f12 11 (by omega), f9 362 (by omega), f9 382 (by omega),
    f11 24 (by omega), f11 25 (by omega), f8 223 (by omega),
    f12 13 (by omega)]

/-- `MOVS` class (first dispatch guard: no predecessors). -/
theorem decodeThumb_movs_eq (hw : UInt16) (h : hw.toNat >>> 11 = 4) :
    decodeThumb hw
      = .movsImm ((hw.toNat >>> 8) &&& 0x7) (hw.toNat &&& 0xFF) := by
  simp [decodeThumb, beq_true_of_eq h]

/-- `CMP` class. -/
theorem decodeThumb_cmp_eq (hw : UInt16) (h : hw.toNat >>> 11 = 5) :
    decodeThumb hw
      = .cmpImm ((hw.toNat >>> 8) &&& 0x7) (hw.toNat &&& 0xFF) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h, f4]

/-- `ADDS` (immediate) class: top `00011`, bit10 set, bit9 clear
    (bit tests in `% 2` normal form: `simp` reduces `&&& 1` to it). -/
theorem decodeThumb_addsImm_eq (hw : UInt16) (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 1) (hl : (hw.toNat >>> 9) % 2 = 0) :
    decodeThumb hw
      = .addsImm (hw.toNat &&& 0x7) ((hw.toNat >>> 3) &&& 0x7)
          ((hw.toNat >>> 6) &&& 0x7) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have fm : (((hw.toNat >>> 10) % 2 == 0) = false) :=
    beq_false_of_ne (by omega)
  have tl : (((hw.toNat >>> 9) % 2 == 0) = true) := beq_true_of_eq hl
  simp [decodeThumb, beq_true_of_eq h11, tl, f4, f5, f6, f7, fm]

/-- `SUBS` (immediate) class: top `00011`, bit10 set, bit9 set. -/
theorem decodeThumb_subsImm_eq (hw : UInt16) (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 1) (hl : (hw.toNat >>> 9) % 2 = 1) :
    decodeThumb hw
      = .subsImm (hw.toNat &&& 0x7) ((hw.toNat >>> 3) &&& 0x7)
          ((hw.toNat >>> 6) &&& 0x7) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have fm : (((hw.toNat >>> 10) % 2 == 0) = false) :=
    beq_false_of_ne (by omega)
  have fl : (((hw.toNat >>> 9) % 2 == 0) = false) :=
    beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h11, f4, f5, f6, f7, fm, fl]

/-- `LSL` (immediate) class. -/
theorem decodeThumb_lsl_eq (hw : UInt16) (h : hw.toNat >>> 11 = 0) :
    decodeThumb hw
      = .lslImm (hw.toNat &&& 0x7) ((hw.toNat >>> 3) &&& 0x7)
          ((hw.toNat >>> 6) &&& 0x1F) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have f3 : ((hw.toNat >>> 11 == 3) = false) := beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h, f4, f5, f6, f7, f3]

/-- `ADDS` (register) class: top `00011`, bit10 clear, bit9 clear. -/
theorem decodeThumb_addsReg_eq (hw : UInt16) (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 0) (hl : (hw.toNat >>> 9) % 2 = 0) :
    decodeThumb hw
      = .addsReg (hw.toNat &&& 0x7) ((hw.toNat >>> 3) &&& 0x7)
          ((hw.toNat >>> 6) &&& 0x7) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have tm : (((hw.toNat >>> 10) % 2 == 0) = true) := beq_true_of_eq hm
  have tl : (((hw.toNat >>> 9) % 2 == 0) = true) := beq_true_of_eq hl
  simp [decodeThumb, beq_true_of_eq h11, tm, tl, f4, f5, f6, f7]

/-- `SUBS` (register) class: top `00011`, bit10 clear, bit9 set. -/
theorem decodeThumb_subsReg_eq (hw : UInt16) (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 0) (hl : (hw.toNat >>> 9) % 2 = 1) :
    decodeThumb hw
      = .subsReg (hw.toNat &&& 0x7) ((hw.toNat >>> 3) &&& 0x7)
          ((hw.toNat >>> 6) &&& 0x7) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have tm : (((hw.toNat >>> 10) % 2 == 0) = true) := beq_true_of_eq hm
  have tl : (((hw.toNat >>> 9) % 2 == 1) = true) := beq_true_of_eq hl
  have fl : (((hw.toNat >>> 9) % 2 == 0) = false) :=
    beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h11, tm, tl, f4, f5, f6, f7, fl]

/-- ALU two-operand class (excluding `MUL`, which is its own cost). -/
theorem decodeThumb_alu2_eq (hw : UInt16) (h10 : hw.toNat >>> 10 = 16)
    (hop : ((hw.toNat >>> 6) &&& 0xF == 13) = false) :
    decodeThumb hw
      = .alu2 ((hw.toNat >>> 6) &&& 0xF) ((hw.toNat >>> 3) &&& 0x7)
          (hw.toNat &&& 0x7) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have f3 : ((hw.toNat >>> 11 == 3) = false) := beq_false_of_ne (by omega)
  have f0 : ((hw.toNat >>> 11 == 0) = false) := beq_false_of_ne (by omega)
  have f1 : ((hw.toNat >>> 11 == 1) = false) := beq_false_of_ne (by omega)
  have f2 : ((hw.toNat >>> 11 == 2) = false) := beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h10, hop,
    f4, f5, f6, f7, f3, f0, f1, f2]

/-- `ADD` (small immediate, single register) class. -/
theorem decodeThumb_addImm_eq (hw : UInt16) (h : hw.toNat >>> 11 = 6) :
    decodeThumb hw
      = .addImm ((hw.toNat >>> 8) &&& 0x7) (hw.toNat &&& 0xFF) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h, f4, f5]

/-- `SUB` (small immediate, single register) class. -/
theorem decodeThumb_subImm_eq (hw : UInt16) (h : hw.toNat >>> 11 = 7) :
    decodeThumb hw
      = .subImm ((hw.toNat >>> 8) &&& 0x7) (hw.toNat &&& 0xFF) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h, f4, f5, f6]

/-- `ASR` (immediate) class (imm5 = 0 maps to 32, as in decode). -/
theorem decodeThumb_asr_eq (hw : UInt16) (h : hw.toNat >>> 11 = 2) :
    decodeThumb hw
      = .asrImm (hw.toNat &&& 0x7) ((hw.toNat >>> 3) &&& 0x7)
          (let sh := (hw.toNat >>> 6) &&& 0x1F; if sh == 0 then 32 else sh) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have f3 : ((hw.toNat >>> 11 == 3) = false) := beq_false_of_ne (by omega)
  have f0 : ((hw.toNat >>> 11 == 0) = false) := beq_false_of_ne (by omega)
  have f1 : ((hw.toNat >>> 11 == 1) = false) := beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h, f4, f5, f6, f7, f3, f0, f1]

/-- Conditional-branch class (excluding `AL`, which decodes to `.nop`,
    and the `SWI` overlap at `v >>> 8 == 223`). -/
theorem decodeThumb_bcond_eq (hw : UInt16) (h12 : hw.toNat >>> 12 = 13)
    (hne : ((hw.toNat >>> 8) &&& 0xF == 14) = false)
    (hswi : ((hw.toNat >>> 8 == 223) = false)) :
    decodeThumb hw
      = .bcond ((hw.toNat >>> 8) &&& 0xF)
          (let raw := hw.toNat &&& 0xFF;
           if raw < 0x80 then (raw : Int) * 2 else ((raw : Int) - 0x100) * 2) := by
  have f (k : Nat) (hk : hw.toNat >>> 11 ≠ k) : ((hw.toNat >>> 11 == k) = false) :=
    beq_false_of_ne hk
  have f10 : ∀ k : Nat, hw.toNat >>> 10 ≠ k → ((hw.toNat >>> 10 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have f12 : ∀ k : Nat, hw.toNat >>> 12 ≠ k → ((hw.toNat >>> 12 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have f9 : ∀ k : Nat, hw.toNat >>> 9 ≠ k → ((hw.toNat >>> 9 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have f8 : ∀ k : Nat, hw.toNat >>> 8 ≠ k → ((hw.toNat >>> 8 == k) = false) :=
    fun k hk => beq_false_of_ne hk
  have t12 : ((hw.toNat >>> 12 == 13) = true) := beq_true_of_eq h12
  simp [decodeThumb, h12, t12, hne, hswi,
    f 4 (by omega), f 5 (by omega), f 6 (by omega), f 7 (by omega),
    f 3 (by omega), f 0 (by omega), f 1 (by omega), f 2 (by omega),
    f10 16 (by omega), f10 17 (by omega),
    f12 5 (by omega),
    f 12 (by omega), f 13 (by omega), f 14 (by omega),
    f 15 (by omega), f 9 (by omega),
    f 16 (by omega), f 17 (by omega), f 18 (by omega),
    f 19 (by omega), f 20 (by omega), f 21 (by omega),
    f12 11 (by omega), f9 362 (by omega), f9 382 (by omega),
    f 24 (by omega), f 25 (by omega)]

/-- `LSR` (immediate) class (imm5 = 0 maps to 32, as in decode). -/
theorem decodeThumb_lsr_eq (hw : UInt16) (h : hw.toNat >>> 11 = 1) :
    decodeThumb hw
      = .lsrImm (hw.toNat &&& 0x7) ((hw.toNat >>> 3) &&& 0x7)
          (let sh := (hw.toNat >>> 6) &&& 0x1F; if sh == 0 then 32 else sh) := by
  have f4 : ((hw.toNat >>> 11 == 4) = false) := beq_false_of_ne (by omega)
  have f5 : ((hw.toNat >>> 11 == 5) = false) := beq_false_of_ne (by omega)
  have f6 : ((hw.toNat >>> 11 == 6) = false) := beq_false_of_ne (by omega)
  have f7 : ((hw.toNat >>> 11 == 7) = false) := beq_false_of_ne (by omega)
  have f3 : ((hw.toNat >>> 11 == 3) = false) := beq_false_of_ne (by omega)
  have f0 : ((hw.toNat >>> 11 == 0) = false) := beq_false_of_ne (by omega)
  simp [decodeThumb, beq_true_of_eq h, f4, f5, f6, f7, f3, f0]

theorem decode_ldr_lit : decodeThumb 0x4B02 = .ldrLit 3 8 := by decide

theorem decode_swi_halt : decodeThumb 0xDF02 = .swi 2 := by decide

theorem decode_lsl : decodeThumb 0x0081 = .lslImm 1 0 2 := by decide

theorem decode_str : decodeThumb 0x601A = .strImm 2 3 0 := by decide

theorem decode_ldr : decodeThumb 0x685B = .ldrImm 3 3 4 := by decide

theorem decode_bx : decodeThumb 0x4770 = .bx 14 := by decide

theorem decode_arm_swi : decodeArm 0xEF000002 = .swi 14 2 := by decide

theorem decode_arm_b : decodeArm 0xEAFFFFFE = .b 14 (-8) := by decide

/-- 0x00000000 is a real instruction (ANDEQ r0,r0,r0), not a nop. -/
theorem decode_arm_and0 : decodeArm 0 = .dpReg 0 0 0 0 0 0 0 false 0 := by decide

-- ── Embedded BIOS IRQ stub decodes as hand-assembled ──

theorem stub_b : decodeArm (bget32LE agbBios 0x18) = .b 14 0x108 := by
  decide

theorem stub_stmfd :
    decodeArm (bget32LE agbBios 0x128)
      = .ldmStm 14 true false false true false 13 0x500F := by
  decide

theorem stub_mov :
    decodeArm (bget32LE agbBios 0x12C) = .dpImm 14 13 0 0 0 3 1 := by
  decide

theorem stub_add :
    decodeArm (bget32LE agbBios 0x130) = .dpImm 14 4 0 15 14 0 0 := by
  decide

theorem stub_ldr :
    decodeArm (bget32LE agbBios 0x134)
      = .memImm 14 true false false false true 0 15 4 := by
  decide

theorem stub_ldmfd :
    decodeArm (bget32LE agbBios 0x138)
      = .ldmStm 14 false true false true true 13 0x500F := by
  decide

theorem stub_subs :
    decodeArm (bget32LE agbBios 0x13C) = .dpImm 14 2 1 14 15 0 4 := by
  decide

/-- Exhaustive: every `MOVS r0,#imm` encoding decodes with exact fields. -/
theorem decode_movs_class :
    ∀ imm : Fin 256, decodeThumb (w16 (0x2000 + imm.val)) = .movsImm 0 imm.val := by
  decide

/-- Exhaustive: every forward `B` encoding (imm11 < 0x400) gives `+2*imm`. -/
theorem decode_b_fwd_class :
    ∀ o : Fin 1024, decodeThumb (w16 (0xE000 + o.val)) = .b ((o.val : Int) * 2) := by
  decide

/-- Exhaustive: every backward `B` encoding gives the negative target. -/
theorem decode_b_back_class :
    ∀ o : Fin 1024,
      decodeThumb (w16 (0xE000 + 0x400 + o.val)) = .b (((o.val : Int) - 1024) * 2) := by
  decide

/-- Exhaustive: every `LDR r0,[PC,#imm]` literal encoding. -/
theorem decode_ldrlit_class :
    ∀ imm : Fin 256,
      decodeThumb (w16 (0x4800 + imm.val)) = .ldrLit 0 (imm.val * 4) := by
  decide

-- ── Phase A: full Thumb spots ──

theorem decode_subs_reg : decodeThumb 0x1A81 = .subsReg 1 0 2 := by decide

theorem decode_cmp : decodeThumb 0x29FF = .cmpImm 1 255 := by decide

theorem decode_add_imm : decodeThumb 0x31FF = .addImm 1 255 := by decide

theorem decode_sub_imm : decodeThumb 0x39FF = .subImm 1 255 := by decide

theorem decode_alu_and : decodeThumb 0x400A = .alu2 0 1 2 := by decide
theorem decode_alu_eor : decodeThumb 0x404A = .alu2 1 1 2 := by decide
theorem decode_alu_lsl : decodeThumb 0x408A = .alu2 2 1 2 := by decide
theorem decode_alu_lsr : decodeThumb 0x40CA = .alu2 3 1 2 := by decide
theorem decode_alu_asr : decodeThumb 0x410A = .alu2 4 1 2 := by decide
theorem decode_alu_adc : decodeThumb 0x414A = .alu2 5 1 2 := by decide
theorem decode_alu_ror : decodeThumb 0x418A = .alu2 6 1 2 := by decide
theorem decode_alu_sbc : decodeThumb 0x41CA = .alu2 7 1 2 := by decide
theorem decode_alu_tst : decodeThumb 0x420A = .alu2 8 1 2 := by decide
theorem decode_alu_neg : decodeThumb 0x424A = .alu2 9 1 2 := by decide
theorem decode_alu_cmp : decodeThumb 0x428A = .alu2 10 1 2 := by decide
theorem decode_alu_cmn : decodeThumb 0x42CA = .alu2 11 1 2 := by decide
theorem decode_alu_orr : decodeThumb 0x430A = .alu2 12 1 2 := by decide
theorem decode_mul : decodeThumb 0x434A = .mul 1 2 := by decide
theorem decode_alu_bic : decodeThumb 0x438A = .alu2 14 1 2 := by decide
theorem decode_alu_mvn : decodeThumb 0x43CA = .alu2 15 1 2 := by decide

theorem decode_hiAdd : decodeThumb 0x44C0 = .hiAdd 8 8 := by decide

theorem decode_hiCmp : decodeThumb 0x4580 = .hiCmp 0 8 := by decide

theorem decode_hiMov : decodeThumb 0x4641 = .hiMov 8 1 := by decide

theorem decode_strReg : decodeThumb 0x5081 = .strReg 1 0 2 := by decide

theorem decode_strhReg : decodeThumb 0x5212 = .strhReg 2 2 0 := by decide

theorem decode_ldsbReg : decodeThumb 0x5612 = .ldsbReg 2 2 0 := by decide

theorem decode_strSp : decodeThumb 0x9108 = .strSp 1 32 := by decide

theorem decode_ldrSp : decodeThumb 0x9908 = .ldrSp 1 32 := by decide

theorem decode_adrPc : decodeThumb 0xA108 = .adrPc 1 32 := by decide

theorem decode_adrSp : decodeThumb 0xA908 = .adrSp 1 32 := by decide

theorem decode_addSp_neg : decodeThumb 0xB087 = .addSp (-28) := by decide

theorem decode_addSp_pos : decodeThumb 0xB006 = .addSp 24 := by decide

theorem decode_push : decodeThumb 0xB401 = .push false 1 := by decide

theorem decode_pop : decodeThumb 0xBC08 = .pop false 8 := by decide

theorem decode_stm : decodeThumb 0xC308 = .stm 3 8 := by decide

theorem decode_ldm : decodeThumb 0xCB08 = .ldm 3 8 := by decide

theorem decode_bcond : decodeThumb 0xD100 = .bcond 1 0 := by decide

theorem decode_blPre : decodeThumb 0xF000 = .blPre 0 := by decide

theorem decode_blSuf : decodeThumb 0xF800 = .blSuf 0 := by decide

/-- BL suffix low half is unsigned: 0xFFB9 means +3954, not −142. -/
theorem decode_blSuf_hi : decodeThumb 0xFFB9 = .blSuf 3954 := by decide

-- ── v4T scope pins: v5/UNDEFINED space decodes to .nop ──

theorem decode_blx_prefix_nop : decodeThumb 0xE800 = .nop := by decide

theorem decode_blx_reg_nop : decodeThumb 0x47E0 = .nop := by decide

theorem decode_bcond_al_nop : decodeThumb 0xDE00 = .nop := by decide

theorem decode_push_gap_nop : decodeThumb 0xB800 = .nop := by decide

-- ── Exhaustive class sweeps: no .nop anywhere in valid space ──

theorem decode_alu_nopfree :
    ∀ w : Fin 1024, decodeThumb (w16 (0x4000 + w.val)) ≠ .nop := by
  decide

theorem decode_hiAdd_nopfree :
    ∀ w : Fin 256, decodeThumb (w16 (0x4400 + w.val)) ≠ .nop := by
  decide

theorem decode_hiCmp_nopfree :
    ∀ w : Fin 256, decodeThumb (w16 (0x4500 + w.val)) ≠ .nop := by
  decide

theorem decode_hiMov_nopfree :
    ∀ w : Fin 256, decodeThumb (w16 (0x4600 + w.val)) ≠ .nop := by
  decide

theorem decode_bcond_nopfree :
    ∀ w : Fin 3584, decodeThumb (w16 (0xD000 + w.val)) ≠ .nop := by
  decide

theorem decode_regmem_nopfree :
    ∀ w : Fin 1024, decodeThumb (w16 (0x5000 + w.val)) ≠ .nop := by
  decide

theorem decode_wordimm_nopfree :
    ∀ w : Fin 4096, decodeThumb (w16 (0x6000 + w.val)) ≠ .nop := by
  decide

theorem decode_hspimm_nopfree :
    ∀ w : Fin 4096, decodeThumb (w16 (0x8000 + w.val)) ≠ .nop := by
  decide

theorem decode_adr_nopfree :
    ∀ w : Fin 1024, decodeThumb (w16 (0xA000 + w.val)) ≠ .nop := by
  decide

theorem decode_addsp_nopfree :
    ∀ w : Fin 256, decodeThumb (w16 (0xB000 + w.val)) ≠ .nop := by
  decide

theorem decode_push_nopfree :
    ∀ w : Fin 512, decodeThumb (w16 (0xB400 + w.val)) ≠ .nop := by
  decide

theorem decode_pop_nopfree :
    ∀ w : Fin 512, decodeThumb (w16 (0xBC00 + w.val)) ≠ .nop := by
  decide

theorem decode_block_nopfree :
    ∀ w : Fin 4096, decodeThumb (w16 (0xC000 + w.val)) ≠ .nop := by
  decide

theorem decode_blpre_nopfree :
    ∀ w : Fin 2048, decodeThumb (w16 (0xF000 + w.val)) ≠ .nop := by
  decide

theorem decode_blsuf_nopfree :
    ∀ w : Fin 2048, decodeThumb (w16 (0xF800 + w.val)) ≠ .nop := by
  decide

-- ── Phase B: ARM spots (all eval-verified above) ──

theorem decode_arm_dpImm : decodeArm 0xE3A00045 = .dpImm 14 13 0 0 0 0 0x45 := by decide

theorem decode_arm_dpReg : decodeArm 0xE0801002 = .dpReg 14 4 0 0 1 2 0 false 0 := by
  decide

theorem decode_arm_dpRegShift : decodeArm 0xE0810312 = .dpReg 14 4 0 1 0 2 0 true 3 := by
  decide

theorem decode_arm_mul : decodeArm 0xE0000291 = .mul 14 false false 0 0 1 2 := by decide

theorem decode_arm_mull : decodeArm 0xE0C12390 = .mull 14 true false false 1 2 0 3 := by
  decide

theorem decode_arm_mrs : decodeArm 0xE10F0000 = .mrs 14 0 0 := by decide

theorem decode_arm_msrImm : decodeArm 0xE328F000 = .msrImm 14 0 8 0 0 := by decide

theorem decode_arm_msrReg : decodeArm 0xE121F000 = .msrReg 14 0 1 0 := by decide

theorem decode_arm_memImm : decodeArm 0xE5910004 = .memImm 14 true true false false true 1 0 4 := by
  decide

theorem decode_arm_memReg : decodeArm 0xE7910002 =
    .memReg 14 true true false false true 1 0 2 0 0 := by
  decide

theorem decode_arm_memH : decodeArm 0xE1D100B4 =
    .memH 14 true true false true true false 1 0 true 4 := by
  decide

theorem decode_arm_memHreg : decodeArm 0xE19100B2 =
    .memH 14 true true false true true false 1 0 false 2 := by
  decide

theorem decode_arm_ldmStm : decodeArm 0xE8A00002 =
    .ldmStm 14 false true false true false 0 2 := by
  decide

theorem decode_arm_b_al : decodeArm 0xEA000000 = .b 14 0 := by decide

theorem decode_arm_bl : decodeArm 0xEB000000 = .bl 14 0 := by decide

/-- Register-form CMP (op 10, S=1) shares bits 27-23 = 00010 with the
    misc/memH class; it must reach DataProc, not `.nop` (the BIOS-boot
    hang: `cmp lr, fp` = 0xE15E000B decoded as nop, flags never set). -/
theorem decode_arm_cmpReg : decodeArm 0xE15E000B = .dpReg 14 10 1 14 0 11 0 false 0 := by
  decide

/-- Register-form TST decodes the same way (op 8, S=1). -/
theorem decode_arm_tstReg : decodeArm 0xE11E000B = .dpReg 14 8 1 14 0 11 0 false 0 := by
  decide

theorem decode_arm_b_ne : decodeArm 0x1A000000 = .b 1 0 := by decide

theorem decode_arm_bx : decodeArm 0xE12FFF10 = .bx 14 0 := by decide

theorem decode_arm_swp : decodeArm 0xE1020091 = .swp 14 false 2 0 1 := by decide

-- ── ARM nop pins: coprocessors, v5 forms, S-less tests ──

theorem decode_arm_cdp_nop : decodeArm 0xEE000000 = .nop := by decide

theorem decode_arm_blx2_nop : decodeArm 0xE12FFF30 = .nop := by decide

theorem decode_arm_tst0_nop : decodeArm 0xE3000001 = .nop := by decide

-- ── ARM class sweeps (constrained domains, exact field maps) ──

theorem decode_arm_dpImm_class :
    ∀ w : Fin 4096,
      decodeArm (w32 (0xE3A00000 + w.val))
        = .dpImm 14 13 0 0 0 ((w.val >>> 8) &&& 0xF) (w.val &&& 0xFF) := by
  decide

theorem decode_arm_dpReg_class :
    ∀ a : Fin 32, ∀ m : Fin 16,
      decodeArm (w32 (0xE0800000 + a.val * 128 + m.val))
        = .dpReg 14 4 0 0 0 m.val 0 false a.val := by
  decide

theorem decode_arm_memImm_class :
    ∀ w : Fin 4096,
      decodeArm (w32 (0xE5910000 + w.val))
        = .memImm 14 true true false false true 1 0 w.val := by
  decide

theorem decode_arm_memReg_class :
    ∀ a : Fin 32, ∀ m : Fin 16,
      decodeArm (w32 (0xE7910000 + a.val * 128 + m.val))
        = .memReg 14 true true false false true 1 0 m.val 0 a.val := by
  decide

theorem decode_arm_memH_class :
    ∀ o : Fin 256,
      decodeArm (w32 (0xE1D100B0 + ((o.val >>> 4) &&& 0xF) * 256 + (o.val &&& 0xF)))
        = .memH 14 true true false true true false 1 0 true o.val := by
  decide

theorem decode_arm_msrImm_class :
    ∀ w : Fin 4096,
      decodeArm (w32 (0xE328F000 + w.val))
        = .msrImm 14 0 8 ((w.val >>> 8) &&& 0xF) (w.val &&& 0xFF) := by
  decide

theorem decode_arm_ldmStm_class :
    ∀ m : Fin 4096,
      decodeArm (w32 (0xE8800000 + m.val)) = .ldmStm 14 false true false false false 0 m.val := by
  decide

end AGB
