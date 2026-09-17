/-
  LeanGameboy.Proofs.Bus — memory-map non-interference.

  Writes to one region never clobber another. Range cases select
  their branch by discharging earlier guards; exact-address cases
  reduce the IO-register match by rewriting the address literal.
-/
import LeanGameboy.Bus

namespace GB

/-- ROM-space writes (MBC registers) preserve WRAM. -/
theorem busWrite_rom_wram (s : GBState) (a : UInt16) (v : UInt8)
    (h : a.toNat < 0x8000) :
    (busWrite s a v).1.wram = s.wram := by
  simp [busWrite, h]

/-- ROM-space writes preserve VRAM. -/
theorem busWrite_rom_vram (s : GBState) (a : UInt16) (v : UInt8)
    (h : a.toNat < 0x8000) :
    (busWrite s a v).1.vram = s.vram := by
  simp [busWrite, h]

/-- ROM-space writes preserve IE. -/
theorem busWrite_rom_ie (s : GBState) (a : UInt16) (v : UInt8)
    (h : a.toNat < 0x8000) :
    (busWrite s a v).1.ie = s.ie := by
  simp [busWrite, h]

/-- VRAM writes preserve WRAM. -/
theorem busWrite_vram_wram (s : GBState) (a : UInt16) (v : UInt8)
    (h1 : 0x8000 <= a.toNat) (h2 : a.toNat < 0xA000) :
    (busWrite s a v).1.wram = s.wram := by
  have e1 : ¬ a.toNat < 0x8000 := by omega
  have e2 : a.toNat < 0xA000 := by omega
  unfold busWrite
  simp only [e1, e2, ite_true, ite_false]
  by_cases hm : s.ppu.mode == 3 <;> simp [hm]

/-- External-RAM writes preserve WRAM. -/
theorem busWrite_sram_wram (s : GBState) (a : UInt16) (v : UInt8)
    (h1 : 0xA000 <= a.toNat) (h2 : a.toNat < 0xC000) :
    (busWrite s a v).1.wram = s.wram := by
  have e1 : ¬ a.toNat < 0x8000 := by omega
  have e2 : ¬ a.toNat < 0xA000 := by omega
  have e3 : a.toNat < 0xC000 := by omega
  unfold busWrite
  simp only [e1, e2, e3, ite_true, ite_false]

/-- WRAM writes preserve VRAM. -/
theorem busWrite_wram_vram (s : GBState) (a : UInt16) (v : UInt8)
    (h1 : 0xC000 <= a.toNat) (h2 : a.toNat < 0xE000) :
    (busWrite s a v).1.vram = s.vram := by
  have e1 : ¬ a.toNat < 0x8000 := by omega
  have e2 : ¬ a.toNat < 0xA000 := by omega
  have e3 : ¬ a.toNat < 0xC000 := by omega
  have e4 : a.toNat < 0xE000 := by omega
  unfold busWrite
  simp only [e1, e2, e3, e4, ite_true, ite_false]

/-- Echo writes preserve VRAM. -/
theorem busWrite_echo_vram (s : GBState) (a : UInt16) (v : UInt8)
    (h1 : 0xE000 <= a.toNat) (h2 : a.toNat < 0xFE00) :
    (busWrite s a v).1.vram = s.vram := by
  have e1 : ¬ a.toNat < 0x8000 := by omega
  have e2 : ¬ a.toNat < 0xA000 := by omega
  have e3 : ¬ a.toNat < 0xC000 := by omega
  have e4 : ¬ a.toNat < 0xE000 := by omega
  have e5 : a.toNat < 0xFE00 := by omega
  unfold busWrite
  simp only [e1, e2, e3, e4, e5, ite_true, ite_false]

/-- HRAM writes preserve WRAM. -/
theorem busWrite_hram_wram (s : GBState) (a : UInt16) (v : UInt8)
    (h1 : 0xFF80 <= a.toNat) (h2 : a.toNat < 0xFFFF) :
    (busWrite s a v).1.wram = s.wram := by
  have e1 : ¬ a.toNat < 0x8000 := by omega
  have e2 : ¬ a.toNat < 0xA000 := by omega
  have e3 : ¬ a.toNat < 0xC000 := by omega
  have e4 : ¬ a.toNat < 0xE000 := by omega
  have e5 : ¬ a.toNat < 0xFE00 := by omega
  have e6 : ¬ a.toNat < 0xFEA0 := by omega
  have e7 : ¬ a.toNat < 0xFF00 := by omega
  have e8 : ¬ a.toNat < 0xFF80 := by omega
  have e9 : a.toNat < 0xFFFF := by omega
  unfold busWrite
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, ite_true, ite_false]

/-- IF writes preserve IE. -/
theorem busWrite_if_ie (s : GBState) (a : UInt16) (v : UInt8)
    (h : a.toNat = 0xFF0F) :
    (busWrite s a v).1.ie = s.ie := by
  simp [busWrite, h]

/-- IE writes preserve IF. -/
theorem busWrite_ie_if (s : GBState) (a : UInt16) (v : UInt8)
    (h : a.toNat = 0xFFFF) :
    (busWrite s a v).1.if_ = s.if_ := by
  simp [busWrite, h]

/-- OAM DMA preserves WRAM and VRAM. -/
theorem oamDma_wram (s : GBState) (src : Nat) :
    (oamDma s src).wram = s.wram := by
  unfold oamDma
  rfl

theorem oamDma_vram (s : GBState) (src : Nat) :
    (oamDma s src).vram = s.vram := by
  unfold oamDma
  rfl

end GB
