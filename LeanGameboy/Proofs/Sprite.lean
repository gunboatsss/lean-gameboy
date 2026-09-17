/-
  LeanGameboy.Proofs.Sprite — OAM attribute decoding.

  Regression proofs for the inverted OBJ priority bug: parsing must
  preserve OAM bit 7 into `Sprite.prio` (bit set = BG/Window colors
  1-3 over OBJ). With the negation, every sprite with `attr = 0`
  rendered behind nonzero background — invisible menu cursors while
  OAM itself updated correctly.
-/
import LeanGameboy.Ppu

namespace GB

/-- Attribute bit 7 is preserved into `prio`. -/
theorem sprite_prio_bit (oam : ByteArray) (i : Nat) :
    (PpuState.parseSprite oam i).prio = bitGet (bget oam (i * 4 + 3)) 7 := by
  unfold PpuState.parseSprite
  simp only []

/-- Attribute Y-flip bit is preserved. -/
theorem sprite_yflip_bit (oam : ByteArray) (i : Nat) :
    (PpuState.parseSprite oam i).yFlip = bitGet (bget oam (i * 4 + 3)) 6 := by
  unfold PpuState.parseSprite
  simp only []

/-- Attribute X-flip bit is preserved. -/
theorem sprite_xflip_bit (oam : ByteArray) (i : Nat) :
    (PpuState.parseSprite oam i).xFlip = bitGet (bget oam (i * 4 + 3)) 5 := by
  unfold PpuState.parseSprite
  simp only []

/-- Attribute palette bit is preserved. -/
theorem sprite_pal_bit (oam : ByteArray) (i : Nat) :
    (PpuState.parseSprite oam i).pal = bitGet (bget oam (i * 4 + 3)) 4 := by
  unfold PpuState.parseSprite
  simp only []

/-- Parsed OAM always holds 40 sprites. -/
theorem parseOam_size (oam : ByteArray) : (PpuState.parseOam oam).size = 40 := by
  simp [PpuState.parseOam]

end GB
