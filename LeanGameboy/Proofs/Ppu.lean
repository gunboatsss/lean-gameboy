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

/-! ## CGB sprite-vs-BG priority (Pan Docs truth table).

`PpuState.cgbMixBgWins` decides per-pixel whether the BG pixel covers the
sprite pixel. The table: transparent BG → OBJ; master clear → OBJ;
both priority bits clear → OBJ; otherwise (opaque BG, master set,
*either* bit set) → BG. -/

/-- Characterization of the mix decision. -/
theorem PpuState.cgbMixBgWins_iff (idx : Nat) (m s g : Bool) :
    PpuState.cgbMixBgWins idx m s g = true ↔
      (idx != 0 ∧ m = true ∧ (s = true ∨ g = true)) := by
  unfold PpuState.cgbMixBgWins
  cases m <;> cases s <;> cases g <;> simp

/-- Transparent BG never wins, regardless of flags. -/
theorem cgbMixBgWins_transparent (m s g : Bool) :
    PpuState.cgbMixBgWins 0 m s g = false := by
  simp [PpuState.cgbMixBgWins]

/-- Master clear: OBJ always wins. -/
theorem cgbMixBgWins_noMaster (idx : Nat) (s g : Bool) :
    PpuState.cgbMixBgWins idx false s g = false := by
  simp [PpuState.cgbMixBgWins]

/-- Both priority bits clear: OBJ wins. -/
theorem cgbMixBgWins_noPrio (idx : Nat) (m : Bool) :
    PpuState.cgbMixBgWins idx m false false = false := by
  cases m <;> simp [PpuState.cgbMixBgWins]

/-- The title-screen case: OAM-priority sprite (bit set, e.g. the
    crystal) over opaque BG (tile bit clear, e.g. the logo) with
    master set → BG/logo wins. -/
theorem PpuState.cgbMixBgWins_title (idx : Nat) (h : idx != 0) :
    PpuState.cgbMixBgWins idx true true false = true := by
  rw [PpuState.cgbMixBgWins_iff]
  exact ⟨h, rfl, Or.inl rfl⟩

/-- Tile priority alone covers a priority-clear sprite. -/
theorem PpuState.cgbMixBgWins_bgPrio (idx : Nat) (h : idx != 0) :
    PpuState.cgbMixBgWins idx true false true = true := by
  rw [PpuState.cgbMixBgWins_iff]
  exact ⟨h, rfl, Or.inr rfl⟩

/-- Pending dispatch picks the lowest set bit: VBlank wins. -/
theorem irqPending_vblank (ie if_ : UInt8)
    (h : bitGet (ie &&& if_) 0 = true) :
    irqPending ie if_ = some 0 := by
  simp [irqPending, h]

end GB
