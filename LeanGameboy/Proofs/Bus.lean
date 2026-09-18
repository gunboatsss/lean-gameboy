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

set_option maxRecDepth 10000

/-- HDMA copies never touch the cycle counter. -/
theorem hdmaCopyStep_cycles (src dst : Nat) (st : GBState) (i : Nat) :
    (hdmaCopyStep src dst st i).cycles = st.cycles := rfl

theorem hdmaFold_cycles (l : List Nat) (src dst : Nat) (st : GBState) :
    (l.foldl (hdmaCopyStep src dst) st).cycles = st.cycles := by
  induction l generalizing st with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons, ih, hdmaCopyStep_cycles]

theorem hdmaBlock_cycles (s : GBState) (src dst : Nat) :
    (hdmaBlock s src dst).cycles = s.cycles := by
  simp [hdmaBlock, hdmaFold_cycles]

theorem hdmaHblank_cycles (s : GBState) :
    (hdmaHblank s).cycles = s.cycles := by
  unfold hdmaHblank
  dsimp only
  split
  · rfl
  · simp [hdmaBlock_cycles]

/-- Scanline completion (HDMA + blit) preserves the cycle counter. -/
theorem finishLine_cycles (s : GBState) (ppu : PpuState) :
    (finishLine s ppu).cycles = s.cycles := by
  unfold finishLine
  dsimp only
  split
  · split <;> simp_all [hdmaHblank_cycles]
  · rfl

/-- Cycle accounting is exact: stepping adds precisely `m` M-cycles.
    (The key composition lemma for any future fuel-sufficiency or
    timing proof; `exec`'s per-arm lower bound remains open.) -/
theorem advance_adds (s : GBState) (m : Nat) :
    (advance s m).cycles = s.cycles + m := by
  unfold advance
  dsimp only
  split
  all_goals split
  all_goals simp_all [finishLine_cycles]

end GB
