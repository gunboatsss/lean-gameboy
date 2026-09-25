/-
  LeanGameboy.Proofs.Framebuffer — framebuffer geometry and PPM sizing.

  `Framebuffer.lean` had zero proof coverage. These pin the DMG
  palette, blank dimensions, single-pixel write bounds/size, and the
  exact `fbToPPM` byte size (header + 3 bytes per pixel — a truncation
  in the headless `--dump` path would fail the size pin).
-/
import LeanGameboy.Framebuffer

namespace GB

-- `decide` over the 23k blank needs headroom.
set_option maxRecDepth 100000

/-! ## Palette + geometry -/

theorem dmgShade_0 : dmgShade 0 = 0xFF9BBC0F := by decide

theorem dmgShade_1 : dmgShade 1 = 0xFF8BAC0F := by decide

theorem dmgShade_2 : dmgShade 2 = 0xFF306230 := by decide

theorem dmgShade_3 : dmgShade 3 = 0xFF0F380F := by decide

theorem dmgShade_other : dmgShade 7 = 0xFF0F380F := by decide

theorem fbPixels : fbWidth * fbHeight = 23040 := by decide

theorem fbBlank_size : fbBlank.size = 23040 := by decide

/-! ## Single-pixel writes -/

/-- Out-of-range x is a no-op. -/
theorem fbSet_oob_x (fb : Array UInt32) (x y : Nat) (c : UInt32)
    (h : fbWidth ≤ x) : fbSet fb x y c = fb := by
  have e : ¬ x < fbWidth := by omega
  simp [fbSet, e]

/-- Out-of-range y is a no-op. -/
theorem fbSet_oob_y (fb : Array UInt32) (x y : Nat) (c : UInt32)
    (h : fbHeight ≤ y) : fbSet fb x y c = fb := by
  have e : ¬ y < fbHeight := by omega
  simp [fbSet, e]

/-- Writes preserve the framebuffer size. -/
theorem fbSet_size (fb : Array UInt32) (x y : Nat) (c : UInt32) :
    (fbSet fb x y c).size = fb.size := by
  unfold fbSet
  split
  · exact Array.size_set! _ _ _
  · rfl

/-! ## PPM dump sizing -/

/-- A fold appending fixed-size chunks grows linearly. -/
theorem foldAppend3_size (l : List Nat) (acc : Array UInt8)
    (f : Nat → Array UInt8) (h : ∀ i, (f i).size = 3) :
    (l.foldl (fun a i => a ++ f i) acc).size
      = acc.size + l.length * 3 := by
  induction l generalizing acc with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [Array.size_append, h]
    omega

/-- The PPM header is 15 bytes. -/
theorem ppmHeader_size :
    ("P6\n160 144\n255\n".toList.toArray.map (fun c => w8 c.toNat)).size
      = 15 := by
  simp

/-- Bridge: `simp` cannot see through projection-of-constructor. -/
theorem byteArray_mk_size (a : Array UInt8) :
    (ByteArray.mk a).size = a.size := rfl

/-- Dumps are exactly header + 3 bytes per pixel. -/
theorem fbToPPM_size (fb : Array UInt32) :
    (fbToPPM fb).size = 15 + 3 * (fbWidth * fbHeight) := by
  have hhdr := ppmHeader_size
  have hempty : ((#[] : Array UInt8)).size = 0 := rfl
  unfold fbToPPM
  dsimp only
  simp only [byteArray_mk_size, Array.size_append, hhdr]
  rw [foldAppend3_size]
  · simp only [hempty, List.length_range]
    omega
  · intro i
    rfl

end GB
