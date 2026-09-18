/-
  LeanGameboy.Proofs.Arith — specifications for the ALU helpers.

  `add8`/`sub8` are transparent definitions, so their flag contracts
  hold by `rfl`. The lemmas below pin those contracts plus identity
  behavior used by later CPU proofs.
-/
import LeanGameboy.Basic

namespace GB

/-- Result value wraps mod 256. -/
theorem add8_val (x y : UInt8) (c : Bool) :
    (add8 x y c).val = w8 (x.toNat + y.toNat + (if c then 1 else 0)) := rfl

/-- Carry iff the true sum exceeds a byte. -/
theorem add8_carry (x y : UInt8) (c : Bool) :
    (add8 x y c).carry = decide (x.toNat + y.toNat + (if c then 1 else 0) > 0xFF) := rfl

/-- Half-carry iff the low nibbles overflow. -/
theorem add8_halfCarry (x y : UInt8) (c : Bool) :
    (add8 x y c).halfCarry =
      decide ((x.toNat % 16) + (y.toNat % 16) + (if c then 1 else 0) >= 16) := rfl

/-- Subtraction mirrors: value, borrow, half-borrow. -/
theorem sub8_val (x y : UInt8) (c : Bool) :
    (sub8 x y c).val = w8 ((x.toNat - y.toNat - (if c then 1 else 0) : Int) % 256).toNat := rfl

/-- Adding zero (no carry-in) is the identity with no flags. -/
theorem add8_zero (x : UInt8) :
    add8 x 0 false = { val := x, halfCarry := false, carry := false } := by
  have h' : x.toNat < 256 := UInt8.toNat_lt_size x
  simp only [add8, w8, AddRes.mk.injEq, decide_eq_false_iff_not,
    UInt8.ofNat_toNat, UInt8.toNat_zero, Nat.add_zero, Nat.zero_mod,
    reduceCtorEq, ite_false]
  exact ⟨trivial, by omega, by omega⟩

/-- Result value in `Nat` terms (composable, unlike the record form). -/
theorem add8_val_toNat (x y : UInt8) :
    (add8 x y false).val.toNat = (x.toNat + y.toNat) % 256 := by
  simp [add8, w8]

/-- Addition is fully commutative (all three components). -/
theorem add8_comm (x y : UInt8) (c : Bool) : add8 x y c = add8 y x c := by
  have e : x.toNat + y.toNat + (if c then 1 else 0)
         = y.toNat + x.toNat + (if c then 1 else 0) := by omega
  have v : (add8 x y c).val = (add8 y x c).val := by simp only [add8_val, e]
  have hc : (add8 x y c).carry = (add8 y x c).carry := by simp only [add8_carry, e]
  have e2 : (x.toNat % 16) + (y.toNat % 16) + (if c then 1 else 0)
          = (y.toNat % 16) + (x.toNat % 16) + (if c then 1 else 0) := by omega
  have hh : (add8 x y c).halfCarry = (add8 y x c).halfCarry := by
    simp only [add8_halfCarry, e2]
  cases e1 : add8 x y c with
  | mk a b cl => cases e2 : add8 y x c with
    | mk d e f => simp_all

/-- Subtracting a value from itself clears everything. -/
theorem sub8_self (x : UInt8) :
    sub8 x x false = { val := 0, halfCarry := false, carry := false } := by
  simp only [sub8, w8, SubRes.mk.injEq, decide_eq_false_iff_not,
    reduceCtorEq, ite_false]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · omega
  · omega

end GB
