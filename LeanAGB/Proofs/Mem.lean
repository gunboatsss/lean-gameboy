/-
  LeanAGB.Proofs.Mem — memory read/write value contracts.

  `Proofs/Bus` pins that writes only touch their own region
  (cycles/regs/rom preservation); here are the value semantics:
  per-region read-after-write roundtrips, cross-region isolation,
  and wide-access instances. (`Proofs/Save` covers mirrors and the
  backup codec at instance level.)
-/
import LeanAGB.Bus

namespace AGB

/-! ## ByteArray read-after-write (local copies: no bare `arr[i]`
     anywhere, so index-proof synthesis never runs). -/

/-- Writes preserve the size. -/
theorem agb_bset_size (b : ByteArray) (i : Nat) (v : UInt8) :
    (bset b i v).size = b.size := by
  unfold bset
  split
  · simp only [ByteArray.set!]
    show (b.data.setIfInBounds i v).size = b.data.size
    exact Array.size_setIfInBounds ..
  · rfl

/-- Reading back the written byte. -/
theorem agb_bget_bset_same (b : ByteArray) (i : Nat) (v : UInt8)
    (hi : i < b.size) :
    bget (bset b i v) i = v := by
  have hsize : (b.set! i v).size = b.size := by
    simp only [ByteArray.set!]
    show (b.data.setIfInBounds i v).size = b.data.size
    exact Array.size_setIfInBounds ..
  have hdi : i < b.data.size := hi
  have h2 := Array.getElem_setIfInBounds (xs := b.data)
    (i := i) (a := v) (j := i) hdi
  simp only [ite_true] at h2
  unfold bget bset
  simp only [hi, hsize, ite_true]
  exact h2

/-- Writes never clobber another address. -/
theorem agb_bget_bset_ne (b : ByteArray) (i j : Nat) (v : UInt8)
    (hi : i < b.size) (hj : j < b.size) (hne : i ≠ j) :
    bget (bset b i v) j = bget b j := by
  have hsize : (b.set! i v).size = b.size := by
    simp only [ByteArray.set!]
    show (b.data.setIfInBounds i v).size = b.data.size
    exact Array.size_setIfInBounds ..
  have hdi : j < b.data.size := hj
  have h2 := Array.getElem_setIfInBounds (xs := b.data)
    (i := i) (a := v) (j := j) hdi
  simp only [hne, ite_false] at h2
  unfold bget bset
  simp only [hi, hj, hsize, ite_true]
  exact h2

/-! ## Per-region roundtrips -/

/-- EWRAM reads back what was written. -/
theorem memRw_ewram (s : AGBState) (addr : UInt32) (v : UInt8)
    (hlo : 0x02000000 ≤ addr.toNat) (hhi : addr.toNat < 0x03000000)
    (hb : mirrorIdx 0x02000000 0x40000 addr.toNat < s.ewram.size) :
    memRead8 (memWrite8 s addr v) addr = v := by
  have e0 : ¬ addr.toNat < 0x4000 := by omega
  have gW : (((decide (0x02000000 ≤ addr.toNat) && decide (addr.toNat < 0x03000000)) = true) = True) := by
    simp [decide_eq_true hlo, decide_eq_true hhi]
  unfold memRead8 memWrite8 memWrite8Nat
  dsimp only
  simp only [e0, gW, ite_true, ite_false]
  exact agb_bget_bset_same _ _ _ hb

/-- IWRAM reads back what was written. -/
theorem memRw_iwram (s : AGBState) (addr : UInt32) (v : UInt8)
    (hlo : 0x03000000 ≤ addr.toNat) (hhi : addr.toNat < 0x04000000)
    (hb : mirrorIdx 0x03000000 0x8000 addr.toNat < s.iwram.size) :
    memRead8 (memWrite8 s addr v) addr = v := by
  have e0 : ¬ addr.toNat < 0x4000 := by omega
  have g1P : ¬ (addr.toNat < 0x03000000) := by omega
  have g1 : (((decide (0x02000000 ≤ addr.toNat) && decide (addr.toNat < 0x03000000)) = true) = False) := by
    simp [decide_eq_false g1P]
  have gW : (((decide (0x03000000 ≤ addr.toNat) && decide (addr.toNat < 0x04000000)) = true) = True) := by
    simp [decide_eq_true hlo, decide_eq_true hhi]
  unfold memRead8 memWrite8 memWrite8Nat
  dsimp only
  simp only [e0, g1, gW, ite_true, ite_false]
  exact agb_bget_bset_same _ _ _ hb

/-- Palette RAM reads back what was written. -/
theorem memRw_pal (s : AGBState) (addr : UInt32) (v : UInt8)
    (hlo : 0x05000000 ≤ addr.toNat) (hhi : addr.toNat < 0x06000000)
    (hb : mirrorIdx 0x05000000 0x400 addr.toNat < s.pal.size) :
    memRead8 (memWrite8 s addr v) addr = v := by
  have e0 : ¬ addr.toNat < 0x4000 := by omega
  have g1P : ¬ (addr.toNat < 0x03000000) := by omega
  have g1 : (((decide (0x02000000 ≤ addr.toNat) && decide (addr.toNat < 0x03000000)) = true) = False) := by
    simp [decide_eq_false g1P]
  have g2P : ¬ (addr.toNat < 0x04000000) := by omega
  have g2 : (((decide (0x03000000 ≤ addr.toNat) && decide (addr.toNat < 0x04000000)) = true) = False) := by
    simp [decide_eq_false g2P]
  have g3P : ¬ (addr.toNat < 0x05000000) := by omega
  have g3 : (((decide (0x04000000 ≤ addr.toNat) && decide (addr.toNat < 0x05000000)) = true) = False) := by
    simp [decide_eq_false g3P]
  have gW : (((decide (0x05000000 ≤ addr.toNat) && decide (addr.toNat < 0x06000000)) = true) = True) := by
    simp [decide_eq_true hlo, decide_eq_true hhi]
  unfold memRead8 memWrite8 memWrite8Nat
  dsimp only
  simp only [e0, g1, g2, g3, gW, ite_true, ite_false]
  exact agb_bget_bset_same _ _ _ hb

/-- VRAM reads back what was written. -/
theorem memRw_vram (s : AGBState) (addr : UInt32) (v : UInt8)
    (hlo : 0x06000000 ≤ addr.toNat) (hhi : addr.toNat < 0x07000000)
    (hb : vramIdx addr.toNat < s.vram.size) :
    memRead8 (memWrite8 s addr v) addr = v := by
  have e0 : ¬ addr.toNat < 0x4000 := by omega
  have g1P : ¬ (addr.toNat < 0x03000000) := by omega
  have g1 : (((decide (0x02000000 ≤ addr.toNat) && decide (addr.toNat < 0x03000000)) = true) = False) := by
    simp [decide_eq_false g1P]
  have g2P : ¬ (addr.toNat < 0x04000000) := by omega
  have g2 : (((decide (0x03000000 ≤ addr.toNat) && decide (addr.toNat < 0x04000000)) = true) = False) := by
    simp [decide_eq_false g2P]
  have g3P : ¬ (addr.toNat < 0x05000000) := by omega
  have g3 : (((decide (0x04000000 ≤ addr.toNat) && decide (addr.toNat < 0x05000000)) = true) = False) := by
    simp [decide_eq_false g3P]
  have g4P : ¬ (addr.toNat < 0x06000000) := by omega
  have g4 : (((decide (0x05000000 ≤ addr.toNat) && decide (addr.toNat < 0x06000000)) = true) = False) := by
    simp [decide_eq_false g4P]
  have gW : (((decide (0x06000000 ≤ addr.toNat) && decide (addr.toNat < 0x07000000)) = true) = True) := by
    simp [decide_eq_true hlo, decide_eq_true hhi]
  unfold memRead8 memWrite8 memWrite8Nat
  dsimp only
  simp only [e0, g1, g2, g3, g4, gW, ite_true, ite_false]
  exact agb_bget_bset_same _ _ _ hb

/-- OAM reads back what was written. -/
theorem memRw_oam (s : AGBState) (addr : UInt32) (v : UInt8)
    (hlo : 0x07000000 ≤ addr.toNat) (hhi : addr.toNat < 0x08000000)
    (hb : mirrorIdx 0x07000000 0x400 addr.toNat < s.oam.size) :
    memRead8 (memWrite8 s addr v) addr = v := by
  have e0 : ¬ addr.toNat < 0x4000 := by omega
  have g1P : ¬ (addr.toNat < 0x03000000) := by omega
  have g1 : (((decide (0x02000000 ≤ addr.toNat) && decide (addr.toNat < 0x03000000)) = true) = False) := by
    simp [decide_eq_false g1P]
  have g2P : ¬ (addr.toNat < 0x04000000) := by omega
  have g2 : (((decide (0x03000000 ≤ addr.toNat) && decide (addr.toNat < 0x04000000)) = true) = False) := by
    simp [decide_eq_false g2P]
  have g3P : ¬ (addr.toNat < 0x05000000) := by omega
  have g3 : (((decide (0x04000000 ≤ addr.toNat) && decide (addr.toNat < 0x05000000)) = true) = False) := by
    simp [decide_eq_false g3P]
  have g4P : ¬ (addr.toNat < 0x06000000) := by omega
  have g4 : (((decide (0x05000000 ≤ addr.toNat) && decide (addr.toNat < 0x06000000)) = true) = False) := by
    simp [decide_eq_false g4P]
  have g5P : ¬ (addr.toNat < 0x07000000) := by omega
  have g5 : (((decide (0x06000000 ≤ addr.toNat) && decide (addr.toNat < 0x07000000)) = true) = False) := by
    simp [decide_eq_false g5P]
  have gW : (((decide (0x07000000 ≤ addr.toNat) && decide (addr.toNat < 0x08000000)) = true) = True) := by
    simp [decide_eq_true hlo, decide_eq_true hhi]
  unfold memRead8 memWrite8 memWrite8Nat
  dsimp only
  simp only [e0, g1, g2, g3, g4, g5, gW, ite_true, ite_false]
  exact agb_bget_bset_same _ _ _ hb

/-! ## Cross-region isolation (values, not just metadata) -/

/-- EWRAM writes are invisible to IWRAM reads. -/
theorem memIso_ewram_iwram (s : AGBState) (a b : UInt32) (v : UInt8)
    (h1 : 0x02000000 ≤ a.toNat) (h2 : a.toNat < 0x03000000)
    (h3 : 0x03000000 ≤ b.toNat) (h4 : b.toNat < 0x04000000) :
    memRead8 (memWrite8 s a v) b = memRead8 s b := by
  have eW : (((decide (0x02000000 ≤ a.toNat) && decide (a.toNat < 0x03000000)) = true) = True) := by
    simp [decide_eq_true h1, decide_eq_true h2]
  have f0 : ¬ b.toNat < 0x4000 := by omega
  have f1P : ¬ (b.toNat < 0x03000000) := by omega
  have f1 : (((decide (0x02000000 ≤ b.toNat) && decide (b.toNat < 0x03000000)) = true) = False) := by
    simp [decide_eq_false f1P]
  have fW : (((decide (0x03000000 ≤ b.toNat) && decide (b.toNat < 0x04000000)) = true) = True) := by
    simp [decide_eq_true h3, decide_eq_true h4]
  unfold memRead8 memWrite8 memWrite8Nat
  dsimp only
  simp only [eW, f0, f1, fW, ite_true, ite_false]

/-- EWRAM writes are invisible to VRAM reads. -/
theorem memIso_ewram_vram (s : AGBState) (a b : UInt32) (v : UInt8)
    (h1 : 0x02000000 ≤ a.toNat) (h2 : a.toNat < 0x03000000)
    (h3 : 0x06000000 ≤ b.toNat) (h4 : b.toNat < 0x07000000) :
    memRead8 (memWrite8 s a v) b = memRead8 s b := by
  have eW : (((decide (0x02000000 ≤ a.toNat) && decide (a.toNat < 0x03000000)) = true) = True) := by
    simp [decide_eq_true h1, decide_eq_true h2]
  have f0 : ¬ b.toNat < 0x4000 := by omega
  have f1P : ¬ (b.toNat < 0x03000000) := by omega
  have f1 : (((decide (0x02000000 ≤ b.toNat) && decide (b.toNat < 0x03000000)) = true) = False) := by
    simp [decide_eq_false f1P]
  have f2P : ¬ (b.toNat < 0x04000000) := by omega
  have f2 : (((decide (0x03000000 ≤ b.toNat) && decide (b.toNat < 0x04000000)) = true) = False) := by
    simp [decide_eq_false f2P]
  have f3P : ¬ (b.toNat < 0x05000000) := by omega
  have f3 : (((decide (0x04000000 ≤ b.toNat) && decide (b.toNat < 0x05000000)) = true) = False) := by
    simp [decide_eq_false f3P]
  have f4P : ¬ (b.toNat < 0x06000000) := by omega
  have f4 : (((decide (0x05000000 ≤ b.toNat) && decide (b.toNat < 0x06000000)) = true) = False) := by
    simp [decide_eq_false f4P]
  have fW : (((decide (0x06000000 ≤ b.toNat) && decide (b.toNat < 0x07000000)) = true) = True) := by
    simp [decide_eq_true h3, decide_eq_true h4]
  unfold memRead8 memWrite8 memWrite8Nat
  dsimp only
  simp only [eW, f0, f1, f2, f3, f4, fW, ite_true, ite_false]

/-! ## Wide accesses -/

/-- Tiny EWRAM window for closed instances. -/
def memTest : AGBState :=
  { ({} : AGBState) with ewram := ByteArray.mk #[0, 0, 0, 0] }

/-- 16-bit EWRAM roundtrip. -/
theorem mem16_roundtrip :
    memRead16 (memWrite16 memTest 0x02000000 0xBEEF) 0x02000000
      = 0xBEEF := by
  decide

/-- 32-bit EWRAM roundtrip. -/
theorem mem32_roundtrip :
    memRead32 (memWrite32 memTest 0x02000000 0xDEADBEEF) 0x02000000
      = 0xDEADBEEF := by
  decide

end AGB
