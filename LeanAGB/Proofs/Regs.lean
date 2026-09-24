/-
  LeanAGB.Proofs.Regs — CPSR codec bit positions (N=31 Z=30 C=29 V=28, T=5).
-/
import LeanAGB.Cpu.Regs

namespace AGB

theorem cpsr_flags_exclusive :
    CPSR_N = 31 ∧ CPSR_Z = 30 ∧ CPSR_C = 29 ∧ CPSR_V = 28 := by
  decide

theorem cpsrT_bit5 : cpsrT 0x20 = true := by decide

theorem cpsrT_arm : cpsrT 0x1F = false := by decide

-- ── Condition-code table (ARM ARM DDI 0100I, §A3.2 cond field) ──
-- CPSR literals: N = 0x80000000, Z = 0x40000000, C = 0x20000000, V = 0x10000000.

theorem cond_eq_t : condPass 0x40000000 0 = true := by decide
theorem cond_eq_f : condPass 0x00000000 0 = false := by decide
theorem cond_ne_t : condPass 0x00000000 1 = true := by decide
theorem cond_cs_t : condPass 0x20000000 2 = true := by decide
theorem cond_cc_t : condPass 0x00000000 3 = true := by decide
theorem cond_mi_t : condPass 0x80000000 4 = true := by decide
theorem cond_pl_t : condPass 0x00000000 5 = true := by decide
theorem cond_vs_t : condPass 0x10000000 6 = true := by decide
theorem cond_vc_t : condPass 0x00000000 7 = true := by decide
theorem cond_hi_t : condPass 0x20000000 8 = true := by decide
theorem cond_hi_f_z : condPass 0x60000000 8 = false := by decide
theorem cond_ls_t : condPass 0x40000000 9 = true := by decide
theorem cond_ge_t : condPass 0x90000000 10 = true := by decide
theorem cond_lt_t : condPass 0x80000000 11 = true := by decide
theorem cond_gt_t : condPass 0x20000000 12 = true := by decide
theorem cond_le_t : condPass 0x40000000 13 = true := by decide

theorem cond_al_never (cpsr : UInt32) : condPass cpsr 14 = false := by
  simp [condPass]

theorem cond_nv_never (cpsr : UInt32) : condPass cpsr 15 = false := by
  simp [condPass]

-- ── ARM condition gate: AL passes, NV never, rest delegate ──

theorem armCond_al (cpsr : UInt32) : armCondPass cpsr 14 = true := by
  simp [armCondPass]

theorem armCond_nv (cpsr : UInt32) : armCondPass cpsr 15 = false := by
  simp [armCondPass, condPass]

theorem armCond_eq : armCondPass 0x40000000 0 = true := by decide

end AGB
