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

/-- HDMA steps never move the stack pointer (same fold pattern). -/
theorem hdmaCopyStep_sp (src dst : Nat) (st : GBState) (i : Nat) :
    (hdmaCopyStep src dst st i).regs.sp = st.regs.sp := rfl

theorem hdmaFold_sp (l : List Nat) (src dst : Nat) (st : GBState) :
    (l.foldl (hdmaCopyStep src dst) st).regs.sp = st.regs.sp := by
  induction l generalizing st with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons, ih, hdmaCopyStep_sp]

theorem hdmaBlock_sp (s : GBState) (src dst : Nat) :
    (hdmaBlock s src dst).regs.sp = s.regs.sp := by
  simp [hdmaBlock, hdmaFold_sp]

theorem hdmaHblank_sp (s : GBState) :
    (hdmaHblank s).regs.sp = s.regs.sp := by
  unfold hdmaHblank
  dsimp only
  split
  · rfl
  · simp [hdmaBlock_sp]

/-- HDMA steps never touch HRAM. -/
theorem hdmaCopyStep_hram (src dst : Nat) (st : GBState) (i : Nat) :
    (hdmaCopyStep src dst st i).hram = st.hram := rfl

theorem hdmaFold_hram (l : List Nat) (src dst : Nat) (st : GBState) :
    (l.foldl (hdmaCopyStep src dst) st).hram = st.hram := by
  induction l generalizing st with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons, ih, hdmaCopyStep_hram]

theorem hdmaBlock_hram (s : GBState) (src dst : Nat) :
    (hdmaBlock s src dst).hram = s.hram := by
  simp [hdmaBlock, hdmaFold_hram]

theorem hdmaHblank_hram (s : GBState) :
    (hdmaHblank s).hram = s.hram := by
  unfold hdmaHblank
  dsimp only
  split
  · rfl
  · simp [hdmaBlock_hram]

/-- Scanline completion (HDMA + blit) preserves the cycle counter. -/
theorem finishLine_cycles (s : GBState) (ppu : PpuState) :
    (finishLine s ppu).cycles = s.cycles := by
  unfold finishLine
  dsimp only
  split
  · split <;> simp_all [hdmaHblank_cycles]
  · rfl

/-- Scanline completion preserves the stack pointer. -/
theorem finishLine_sp (s : GBState) (ppu : PpuState) :
    (finishLine s ppu).regs.sp = s.regs.sp := by
  unfold finishLine
  dsimp only
  split
  · split <;> simp_all [hdmaHblank_sp]
  · rfl

/-- Scanline completion preserves HRAM. -/
theorem finishLine_hram (s : GBState) (ppu : PpuState) :
    (finishLine s ppu).hram = s.hram := by
  unfold finishLine
  dsimp only
  split
  · split <;> simp_all [hdmaHblank_hram]
  · rfl

/-- Cycle accounting is exact: stepping adds precisely `m` M-cycles.
    (The key composition lemma for any future fuel-sufficiency or
    timing proof; pair with `exec_cycles_pos` below.) -/
theorem advance_adds (s : GBState) (m : Nat) :
    (advance s m).cycles = s.cycles + m := by
  unfold advance
  dsimp only
  split
  all_goals split
  all_goals simp_all [finishLine_cycles]

/-- Push `.2` through `ite` so `split` can see branch costs.
    (Unlike general `apply_ite`, this fires only on `Prod.snd` and so
    cannot ping-pong with the `exec` equation lemmas.) -/
theorem snd_ite (c : Prop) [Decidable c] (a b : GBState × Nat) :
    (if c then a else b).2 = if c then a.2 else b.2 := by
  by_cases h : c <;> simp [h]

/-- Every instruction costs at least one M-cycle: the per-arm lower
    bound behind any fuel-sufficiency argument (`runUntilCycles` relies
    on `cycles` strictly increasing). Uniform automation: plain arms
    reduce to a literal or `base + sub-cost` (`omega`); `ite` arms split
    open; the four `Option`-payload arms (`Jr`/`Jp`/`Call`/`Ret`) first
    case their payload so the right equation lemma fires; `Halt`'s
    `match` on the pending interrupt is cased by term. -/
theorem exec_cycles_pos (s : GBState) (i : Instr) (pc : UInt16) :
    1 ≤ (exec s i pc).2 := by
  cases i <;> simp only [exec, snd_ite] <;> (try dsimp only) <;>
    first
    | omega
    | (cases ‹Option Cond› <;> (try simp only [snd_ite]) <;> (try dsimp only) <;>
        first | omega | (split <;> first | omega | (split <;> omega)))
    | (split <;> first | omega | (split <;> first | omega | (split <;> omega)))
    | (cases h : irqPending s.ie s.if_ <;> (try simp only [h, snd_ite]) <;> (try dsimp only) <;>
        first | omega | (split <;> first | omega | (split <;> omega)))

end GB
