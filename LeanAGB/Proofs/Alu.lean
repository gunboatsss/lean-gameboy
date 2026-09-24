/-
  LeanAGB.Proofs.Alu — 32-bit ALU flag contracts.
  Instances pin exact NZCV outputs; general lemmas characterize each
  flag in terms of the underlying arithmetic (zero sorry/axiom).
-/
import LeanAGB.Bus

namespace AGB

-- ── Closed instances (ARM ARM §A2 semantics) ──

theorem add_zero :
    add32Flags 0 0 = (0, { n := false, z := true, c := false, v := false }) := by
  decide

theorem add_carry_out :
    add32Flags 0xFFFFFFFF 1 = (0, { n := false, z := true, c := true, v := false }) := by
  decide

theorem add_signed_overflow :
    add32Flags 0x7FFFFFFF 1 =
      (0x80000000, { n := true, z := false, c := false, v := true }) := by
  decide

theorem add_neg_overflow :
    add32Flags 0x80000000 0x80000000 =
      (0, { n := false, z := true, c := true, v := true }) := by
  decide

theorem add_hello :
    add32Flags 0x45 0x38 = (0x7D, { n := false, z := false, c := false, v := false }) := by
  decide

theorem sub_zero :
    sub32Flags 5 5 = (0, { n := false, z := true, c := true, v := false }) := by
  decide

theorem sub_borrow :
    sub32Flags 0 1 =
      (0xFFFFFFFF, { n := true, z := false, c := false, v := false }) := by
  decide

theorem sub_signed_overflow :
    sub32Flags 0x80000000 1 =
      (0x7FFFFFFF, { n := false, z := false, c := true, v := true }) := by
  decide

-- ── General flag characterization ──

theorem add_z_iff (x y : UInt32) : (add32Flags x y).2.z = ((x + y) == 0) := by
  simp [add32Flags]

theorem add_n_is_bit31 (x y : UInt32) :
    (add32Flags x y).2.n = bitGet32 (x + y) 31 := by
  simp [add32Flags]

theorem sub_z_iff (x y : UInt32) : (sub32Flags x y).2.z = ((x - y) == 0) := by
  simp [sub32Flags]

theorem sub_n_is_bit31 (x y : UInt32) :
    (sub32Flags x y).2.n = bitGet32 (x - y) 31 := by
  simp [sub32Flags]

/-- Carry out of ADD = wraparound in Nat (no carry-in in milestone). -/
theorem add_c_iff (x y : UInt32) :
    (add32Flags x y).2.c = decide ((x + y).toNat < x.toNat) := by
  simp [add32Flags]

/-- Carry of SUB = NOT borrow. -/
theorem sub_c_iff (x y : UInt32) :
    (sub32Flags x y).2.c = decide (x.toNat ≥ y.toNat) := by
  simp [sub32Flags]

/-- Value projection: the model returns plain `x + y` / `x - y`. -/
theorem add_val (x y : UInt32) : (add32Flags x y).1 = x + y := by
  rfl

theorem sub_val (x y : UInt32) : (sub32Flags x y).1 = x - y := by
  rfl

end AGB
