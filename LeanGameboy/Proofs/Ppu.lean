/-
  LeanGameboy.Proofs.Ppu — PPU mode and palette properties.
-/
import LeanGameboy.Ppu
import LeanGameboy.Interrupts

namespace GB

/-- LY ≥ 144 means VBlank mode. -/
theorem ppu_mode_vblank (p : PpuState) (h : 144 <= p.ly.toNat) :
    p.curMode = 1 := by
  simp [PpuState.curMode, h]

/-- Acknowledge clears the VBlank request. -/
theorem ppu_ack (p : PpuState) : p.ackVblank.vblankIrq = false := rfl

/-- Palette mapping always yields a valid shade. -/
theorem palMap_lt (pal : UInt8) (idx : Nat) : PpuState.palMap pal idx < 4 := by
  unfold PpuState.palMap
  omega

/-- Interrupt vectors follow the 0x40 + 8·bit layout. -/
theorem irqVector_layout (b : Nat) : irqVector b = w16 (0x40 + 8 * b) := rfl

/-- Pending dispatch picks the lowest set bit: VBlank wins. -/
theorem irqPending_vblank (ie if_ : UInt8)
    (h : bitGet (ie &&& if_) 0 = true) :
    irqPending ie if_ = some 0 := by
  simp [irqPending, h]

end GB
