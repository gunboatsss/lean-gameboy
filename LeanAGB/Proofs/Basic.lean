/-
  LeanAGB.Proofs.Basic — kernel-checked contracts for bit helpers.
  Zero sorry/axiom, same gate as LeanGameboy.Proofs.
-/
import LeanAGB.Basic

namespace AGB

theorem rotr32_zero (x : UInt32) : rotr32 x 0 = x := by
  simp [rotr32]

theorem rotr32_full (x : UInt32) : rotr32 x 32 = x := by
  simp [rotr32]

theorem signExt_small : signExt 5 4 = 5 := by decide

theorem signExt_neg : signExt 0xB 4 = -5 := by decide

theorem bgr555_black : bgr555ToARGB 0 = 0xFF000000 := by decide

theorem bgr555_red : bgr555ToARGB 0x001F = 0xFFFF0000 := by decide

theorem bgr555_green : bgr555ToARGB 0x03E0 = 0xFF00FF00 := by decide

theorem bgr555_blue : bgr555ToARGB 0x7C00 = 0xFF0000FF := by decide

theorem bgr555_white : bgr555ToARGB 0x7FFF = 0xFFFFFFFF := by decide

theorem add_identity_nat (n : Nat) : n + 0 = n := by simp

/-- `UInt16` round-trip through `Nat` (halfword addresses stay in range). -/
theorem w16_toNat (x : Nat) : (w16 x).toNat = x % 65536 := by
  simp [w16]

theorem u16_160_toNat : (160 : UInt16).toNat = 160 := by decide

theorem u16_0_toNat : (0 : UInt16).toNat = 0 := by decide

-- ── Register-list / popcount (block transfers) ──

theorem regList_empty : regList 0 = [] := by decide

theorem regList_full : regList 0xFF = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem regList_two : regList 0x03 = [0, 1] := by decide

theorem regList_hi : regList 0x81 = [0, 7] := by decide

theorem popcount_full : popcount 0xFF = 8 := by decide

theorem popcount_empty : popcount 0 = 0 := by decide

theorem popcount_two : popcount 0x03 = 2 := by decide

-- ── Shift-with-carry edges (barrel shifter) ──

theorem lsl_carry : lslRC 0x80000000 1 false = (0, true) := by decide

theorem lsl_identity : lslRC 0x12345678 0 true = (0x12345678, true) := by decide

theorem lsl_overflow32 : lslRC 0xFFFFFFFF 32 false = (0, true) := by decide

theorem lsr_32rule : lsrRC 0x80000000 32 false = (0, true) := by decide

theorem lsr_carry : lsrRC 0x00000001 1 false = (0, true) := by decide

theorem asr_sign : asrRC 0x80000000 1 false = (0xC0000000, false) := by decide

theorem asr_32fill : asrRC 0x80000000 32 false = (0xFFFFFFFF, true) := by decide

theorem ror_wrap : rorRC 0x80000001 1 false = (0xC0000000, true) := by decide

theorem ror_mult32 : rorRC 0x80000001 32 false = (0x80000001, true) := by decide

-- ── Sign extension (LDSB/LDSH) ──

theorem sx8_neg : sx8 0xFF = 0xFFFFFFFF := by decide

theorem sx8_pos : sx8 0x7F = 0x0000007F := by decide

theorem sx16_neg : sx16 0x8000 = 0xFFFF8000 := by decide

theorem sx16_pos : sx16 0x7FFF = 0x00007FFF := by decide

-- ── RRX / register shifts / 16-bit masks (ARM executor) ──

theorem rrx_nocarry : rrxRC 0x00000001 false = (0, true) := by decide

theorem rrx_carry_set : rrxRC 0 true = (0x80000000, false) := by decide

theorem armShift_lsl_reg : armShiftReg 0 1 3 false = (8, false) := by decide

theorem armShift_ror_mod : armShiftReg 3 0x80000001 33 false = (0xC0000000, true) := by decide

theorem regList16_empty : regList16 0 = [] := by decide

theorem popcount16_full : popcount16 0xFFFF = 16 := by decide

theorem popcount16_empty : popcount16 0 = 0 := by decide

end AGB
