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

/-! ## Fetch helpers -/

/-- A tile pixel is always a 2-bit shade. -/
theorem tilePix_lt (vram : ByteArray) (base i : Nat) :
    PpuState.tilePix vram base i < 4 := by
  unfold PpuState.tilePix
  dsimp only
  split
  · split <;> omega
  · split <;> omega

/-- Unsigned tile data lives at `id * 16`. -/
theorem tileAddr_unsigned (id : UInt8) :
    PpuState.tileAddr false id = id.toNat * 16 := rfl

/-- Signed tile 0 starts at `0x1000`. -/
theorem tileAddr_signed_zero : PpuState.tileAddr true 0 = 0x1000 := by
  decide

/-- Signed tile `0xFF` is the last block (`0x0FF0`). -/
theorem tileAddr_signed_last : PpuState.tileAddr true 0xFF = 0x0FF0 := by
  decide

/-- `0xE4` is the identity palette. -/
theorem palMap_identity_0 : PpuState.palMap 0xE4 0 = 0 := by decide

theorem palMap_identity_1 : PpuState.palMap 0xE4 1 = 1 := by decide

theorem palMap_identity_2 : PpuState.palMap 0xE4 2 = 2 := by decide

theorem palMap_identity_3 : PpuState.palMap 0xE4 3 = 3 := by decide

/-- Palette colors read back in bounds, white out of bounds. -/
theorem palColor_hit : PpuState.palColor #[10, 20, 30] 1 = 20 := by decide

theorem palColor_miss : PpuState.palColor #[] 5 = 0x7FFF := by decide

/-! ## OAM / attribute decoding -/

/-- Sprite position and tile decode per byte. -/
theorem parseSprite_pos :
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).y = 10 ∧
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).x = 20 ∧
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).tile = 5 := by
  decide

/-- Attribute `0xE4`: behind, both flips, OBP0, CGB palette 4. -/
theorem parseSprite_attr :
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).prio = true ∧
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).yFlip = true ∧
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).xFlip = true ∧
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).pal = false ∧
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).cgbPal = 4 ∧
    (PpuState.parseSprite (ByteArray.mk #[10, 20, 5, 0xE4]) 0).vbank = 0 := by
  decide

/-- CGB map attribute decode. -/
theorem parseBgAttr_pins :
    PpuState.parseBgAttr 0xE4
      = { pal := 4, bank := 0, xFlip := true, yFlip := true,
          prio := true } := by
  decide

/-- Sprite priority alone covers an opaque BG pixel. -/
theorem PpuState.cgbMixBgWins_sprite (idx : Nat) (h : idx != 0) :
    PpuState.cgbMixBgWins idx true true false = true := by
  rw [PpuState.cgbMixBgWins_iff]
  exact ⟨h, rfl, Or.inl rfl⟩

/-! ## STAT modes -/

/-- Dots 0-79 of a visible line: OAM scan. -/
theorem curMode_oam (p : PpuState) (hly : p.ly.toNat < 144)
    (hd : p.dots < 80) : p.curMode = 2 := by
  have e0 : ¬ 144 ≤ p.ly.toNat := by omega
  unfold PpuState.curMode
  rw [ite_eq_right e0, ite_eq_left hd]

/-- Dots 80-251: drawing. -/
theorem curMode_draw (p : PpuState) (hly : p.ly.toNat < 144)
    (h1 : 80 ≤ p.dots) (h2 : p.dots < 252) : p.curMode = 3 := by
  have e0 : ¬ 144 ≤ p.ly.toNat := by omega
  have e1 : ¬ p.dots < 80 := by omega
  unfold PpuState.curMode
  rw [ite_eq_right e0, ite_eq_right e1, ite_eq_left h2]

/-- Dots 252+: HBlank. -/
theorem curMode_hblank (p : PpuState) (hly : p.ly.toNat < 144)
    (hd : 252 ≤ p.dots) : p.curMode = 0 := by
  have e0 : ¬ 144 ≤ p.ly.toNat := by omega
  have e1 : ¬ p.dots < 80 := by omega
  have e2 : ¬ p.dots < 252 := by omega
  unfold PpuState.curMode
  rw [ite_eq_right e0, ite_eq_right e1, ite_eq_right e2]

/-! ## LCD-off step: frozen, no flags -/

/-- LCD off freezes position registers. -/
theorem step_lcdoff (p : PpuState) (dots : Nat)
    (h : bitGet p.lcdc 7 = false) (hz : (dots == 0) = false) :
    (p.step dots).1.ly = 0 ∧ (p.step dots).1.dots = 0 ∧
    (p.step dots).1.mode = 0 := by
  have e0 : ¬ ((dots == 0) = true) := by simp [hz]
  have e1 : ((!bitGet p.lcdc 7) = true) := by simp [h]
  unfold PpuState.step
  dsimp only
  rw [ite_eq_right e0, ite_eq_left e1]
  exact ⟨rfl, rfl, rfl⟩

/-- LCD off raises no edges. -/
theorem step_lcdoff_flags (p : PpuState) (dots : Nat)
    (h : bitGet p.lcdc 7 = false) (hz : (dots == 0) = false) :
    (p.step dots).2.1 = false ∧ (p.step dots).2.2.1 = false ∧
    (p.step dots).2.2.2.1 = false ∧ (p.step dots).2.2.2.2 = false := by
  have e0 : ¬ ((dots == 0) = true) := by simp [hz]
  have e1 : ((!bitGet p.lcdc 7) = true) := by simp [h]
  unfold PpuState.step
  dsimp only
  rw [ite_eq_right e0, ite_eq_left e1]
  exact ⟨rfl, rfl, rfl, rfl⟩

end GB
