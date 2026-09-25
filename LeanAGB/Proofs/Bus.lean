/-
  LeanAGB.Proofs.Bus — memory-map non-interference, IRQ register
  semantics, and exact cycle accounting. All structural: writes only
  touch their own region; `advance` accounts cycles exactly.
-/
import LeanAGB.Bus

namespace AGB

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

-- ── Write preservation (a write never touches other device state) ──
-- Pattern: `unfold` + pure zeta (`simp only []`) keeps plain `ite`s that
-- `split` can case; full `simp` would build `dite`s that defeat it.

theorem saveWrite8_cycles (s : AGBState) (off : Nat) (v : UInt8) :
    (saveWrite8 s off v).cycles = s.cycles := by
  unfold saveWrite8
  split <;> rfl

theorem saveWrite8_regs (s : AGBState) (off : Nat) (v : UInt8) :
    (saveWrite8 s off v).regs = s.regs := by
  unfold saveWrite8
  split <;> rfl

theorem saveWrite8_rom (s : AGBState) (off : Nat) (v : UInt8) :
    (saveWrite8 s off v).rom = s.rom := by
  unfold saveWrite8
  split <;> rfl

theorem saveWrite8_timers (s : AGBState) (off : Nat) (v : UInt8) :
    (saveWrite8 s off v).timers = s.timers := by
  unfold saveWrite8
  split <;> rfl

-- ── IO-sync helpers preserve unrelated state (declared before use) ──

theorem syncTimer16_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncTimer16 s a v).cycles = s.cycles := by
  unfold syncTimer16 syncTimerReload syncTimerCtrl
  simp only []
  repeat (first | split | rfl)

theorem syncTimer16_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncTimer16 s a v).regs = s.regs := by
  unfold syncTimer16 syncTimerReload syncTimerCtrl
  simp only []
  repeat (first | split | rfl)

theorem syncTimer16_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncTimer16 s a v).rom = s.rom := by
  unfold syncTimer16 syncTimerReload syncTimerCtrl
  simp only []
  repeat (first | split | rfl)

theorem syncDmaCh_cycles (s : AGBState) (idx base a : Nat) (v : UInt16) :
    (syncDmaCh s idx base a v).cycles = s.cycles := by
  unfold syncDmaCh
  simp only []
  repeat (first | split | rfl)

theorem syncDmaCh_regs (s : AGBState) (idx base a : Nat) (v : UInt16) :
    (syncDmaCh s idx base a v).regs = s.regs := by
  unfold syncDmaCh
  simp only []
  repeat (first | split | rfl)

theorem syncDmaCh_rom (s : AGBState) (idx base a : Nat) (v : UInt16) :
    (syncDmaCh s idx base a v).rom = s.rom := by
  unfold syncDmaCh
  simp only []
  repeat (first | split | rfl)

theorem syncDma16_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncDma16 s a v).cycles = s.cycles := by
  simp [syncDma16, syncDmaCh_cycles]

theorem syncDma16_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncDma16 s a v).regs = s.regs := by
  simp [syncDma16, syncDmaCh_regs]

theorem syncDma16_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncDma16 s a v).rom = s.rom := by
  simp [syncDma16, syncDmaCh_rom]

-- ── BG sync (moved before DMA users) --

theorem syncBgCnt_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgCnt s a v).cycles = s.cycles := by
  unfold syncBgCnt
  simp only []
  repeat (first | split | rfl)

theorem syncBgCnt_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgCnt s a v).regs = s.regs := by
  unfold syncBgCnt
  simp only []
  repeat (first | split | rfl)

theorem syncBgCnt_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgCnt s a v).rom = s.rom := by
  unfold syncBgCnt
  simp only []
  repeat (first | split | rfl)

theorem syncBgHo_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgHo s a v).cycles = s.cycles := by
  unfold syncBgHo
  simp only []
  repeat (first | split | rfl)

theorem syncBgHo_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgHo s a v).regs = s.regs := by
  unfold syncBgHo
  simp only []
  repeat (first | split | rfl)

theorem syncBgHo_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgHo s a v).rom = s.rom := by
  unfold syncBgHo
  simp only []
  repeat (first | split | rfl)

theorem syncBgVo_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgVo s a v).cycles = s.cycles := by
  unfold syncBgVo
  simp only []
  repeat (first | split | rfl)

theorem syncBgVo_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgVo s a v).regs = s.regs := by
  unfold syncBgVo
  simp only []
  repeat (first | split | rfl)

theorem syncBgVo_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBgVo s a v).rom = s.rom := by
  unfold syncBgVo
  simp only []
  repeat (first | split | rfl)

theorem syncBg16_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBg16 s a v).cycles = s.cycles := by
  simp [syncBg16, syncBgCnt_cycles, syncBgHo_cycles, syncBgVo_cycles]

theorem syncBg16_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBg16 s a v).regs = s.regs := by
  simp [syncBg16, syncBgCnt_regs, syncBgHo_regs, syncBgVo_regs]

theorem syncBg16_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBg16 s a v).rom = s.rom := by
  simp [syncBg16, syncBgCnt_rom, syncBgHo_rom, syncBgVo_rom]

theorem syncBld16_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBld16 s a v).cycles = s.cycles := by
  unfold syncBld16
  simp only []
  repeat (first | split | rfl)

theorem syncApu16_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncApu16 s a v).cycles = s.cycles := by
  unfold syncApu16
  repeat (first | split | rfl)

theorem syncApu16_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncApu16 s a v).regs = s.regs := by
  unfold syncApu16
  repeat (first | split | rfl)

theorem syncApu16_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncApu16 s a v).rom = s.rom := by
  unfold syncApu16
  repeat (first | split | rfl)

theorem syncApu16_ppu (s : AGBState) (a : Nat) (v : UInt16) :
    (syncApu16 s a v).ppu = s.ppu := by
  unfold syncApu16
  repeat (first | split | rfl)

theorem syncBld16_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBld16 s a v).regs = s.regs := by
  unfold syncBld16
  simp only []
  repeat (first | split | rfl)

theorem syncBld16_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncBld16 s a v).rom = s.rom := by
  unfold syncBld16
  simp only []
  repeat (first | split | rfl)

theorem syncIo16_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (syncIo16 s a v).cycles = s.cycles := by
  unfold syncIo16
  simp only []
  repeat (first | simp [syncBg16_cycles, syncTimer16_cycles, syncDma16_cycles,
    syncApu16_cycles, syncBld16_cycles] | split | rfl)

theorem syncIo16_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (syncIo16 s a v).regs = s.regs := by
  unfold syncIo16
  simp only []
  repeat (first | simp [syncBg16_regs, syncTimer16_regs, syncDma16_regs,
    syncApu16_regs, syncBld16_regs] | split | rfl)

theorem syncIo16_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (syncIo16 s a v).rom = s.rom := by
  unfold syncIo16
  simp only []
  repeat (first | simp [syncBg16_rom, syncTimer16_rom, syncDma16_rom,
    syncApu16_rom, syncBld16_rom] | split | rfl)

-- ── DMA engine preservation (Phase 1; mirrors pushRegs/popRegs style) ──

theorem apuFifoPush_cycles (s : AGBState) (w : Nat) (v : UInt8) :
    (apuFifoPush s w v).cycles = s.cycles := by
  unfold apuFifoPush
  split <;> rfl

theorem apuFifoPush_regs (s : AGBState) (w : Nat) (v : UInt8) :
    (apuFifoPush s w v).regs = s.regs := by
  unfold apuFifoPush
  split <;> rfl

theorem apuFifoPush_rom (s : AGBState) (w : Nat) (v : UInt8) :
    (apuFifoPush s w v).rom = s.rom := by
  unfold apuFifoPush
  split <;> rfl

theorem memWrite8IO_cycles (s : AGBState) (a : Nat) (v : UInt8) :
    (memWrite8IO s a v).cycles = s.cycles := by
  unfold memWrite8IO
  simp only []
  repeat (first | simp [syncIo16_cycles, apuFifoPush_cycles] | split | rfl)

theorem memWrite8IO_regs (s : AGBState) (a : Nat) (v : UInt8) :
    (memWrite8IO s a v).regs = s.regs := by
  unfold memWrite8IO
  simp only []
  repeat (first | simp [syncIo16_regs, apuFifoPush_regs] | split | rfl)

theorem memWrite8IO_rom (s : AGBState) (a : Nat) (v : UInt8) :
    (memWrite8IO s a v).rom = s.rom := by
  unfold memWrite8IO
  simp only []
  repeat (first | simp [syncIo16_rom, apuFifoPush_rom] | split | rfl)

theorem withEwram_cycles (s : AGBState) (f : ByteArray → ByteArray) :
    (withEwram s f).cycles = s.cycles := by unfold withEwram; rfl
theorem withIwram_cycles (s : AGBState) (f : ByteArray → ByteArray) :
    (withIwram s f).cycles = s.cycles := by unfold withIwram; rfl
theorem withPal_cycles (s : AGBState) (f : ByteArray → ByteArray) :
    (withPal s f).cycles = s.cycles := by unfold withPal; rfl
theorem withVram_cycles (s : AGBState) (f : ByteArray → ByteArray) :
    (withVram s f).cycles = s.cycles := by unfold withVram; rfl
theorem withOam_cycles (s : AGBState) (f : ByteArray → ByteArray) :
    (withOam s f).cycles = s.cycles := by unfold withOam; rfl
theorem withEwram_regs (s : AGBState) (f : ByteArray → ByteArray) :
    (withEwram s f).regs = s.regs := by unfold withEwram; rfl
theorem withIwram_regs (s : AGBState) (f : ByteArray → ByteArray) :
    (withIwram s f).regs = s.regs := by unfold withIwram; rfl
theorem withPal_regs (s : AGBState) (f : ByteArray → ByteArray) :
    (withPal s f).regs = s.regs := by unfold withPal; rfl
theorem withVram_regs (s : AGBState) (f : ByteArray → ByteArray) :
    (withVram s f).regs = s.regs := by unfold withVram; rfl
theorem withOam_regs (s : AGBState) (f : ByteArray → ByteArray) :
    (withOam s f).regs = s.regs := by unfold withOam; rfl
theorem withEwram_rom (s : AGBState) (f : ByteArray → ByteArray) :
    (withEwram s f).rom = s.rom := by unfold withEwram; rfl
theorem withIwram_rom (s : AGBState) (f : ByteArray → ByteArray) :
    (withIwram s f).rom = s.rom := by unfold withIwram; rfl
theorem withPal_rom (s : AGBState) (f : ByteArray → ByteArray) :
    (withPal s f).rom = s.rom := by unfold withPal; rfl
theorem withVram_rom (s : AGBState) (f : ByteArray → ByteArray) :
    (withVram s f).rom = s.rom := by unfold withVram; rfl
theorem withOam_rom (s : AGBState) (f : ByteArray → ByteArray) :
    (withOam s f).rom = s.rom := by unfold withOam; rfl

theorem memWrite8Nat_cycles (s : AGBState) (a : Nat) (v : UInt8) :
    (memWrite8Nat s a v).cycles = s.cycles := by
  unfold memWrite8Nat
  simp only []
  repeat (first | simp [saveWrite8_cycles, memWrite8IO_cycles] | split | rfl)

theorem memWrite8Nat_regs (s : AGBState) (a : Nat) (v : UInt8) :
    (memWrite8Nat s a v).regs = s.regs := by
  unfold memWrite8Nat
  simp only []
  repeat (first | simp [saveWrite8_regs, memWrite8IO_regs] | split | rfl)

theorem memWrite8Nat_rom (s : AGBState) (a : Nat) (v : UInt8) :
    (memWrite8Nat s a v).rom = s.rom := by
  unfold memWrite8Nat
  simp only []
  repeat (first | simp [saveWrite8_rom, memWrite8IO_rom] | split | rfl)

theorem apuFifoWrite32_cycles (s : AGBState) (w : Nat) (v : UInt32) :
    (apuFifoWrite32 s w v).cycles = s.cycles := by
  simp [apuFifoWrite32, apuFifoPush_cycles]

theorem soundDmaWords_cycles (s : AGBState) (sad : UInt32) (w k : Nat)
    (step : Int) : ((soundDmaWords s sad w k step).1).cycles = s.cycles := by
  induction k generalizing s sad with
  | zero => rfl
  | succ k ih => simp only [soundDmaWords, ih, apuFifoWrite32_cycles]

theorem apuSoundDma_cycles (s : AGBState) (w : Nat) :
    (apuSoundDma s w).cycles = s.cycles := by
  unfold apuSoundDma
  repeat (first | split | simp [soundDmaWords_cycles] | rfl)

theorem apuFifoTick_cycles (s : AGBState) (w i : Nat) :
    (apuFifoTick s w i).cycles = s.cycles := by
  unfold apuFifoTick
  repeat (first | split | simp [apuSoundDma_cycles] | rfl)

theorem apuTimerOverflow_cycles (s : AGBState) (i n : Nat) :
    (apuTimerOverflow s i n).cycles = s.cycles := by
  induction n generalizing s with
  | zero => rfl
  | succ o ih => simp only [apuTimerOverflow, ih, apuFifoTick_cycles]

theorem dmaWrite8IO_cycles (s : AGBState) (a : Nat) (v : UInt8) :
    (dmaWrite8IO s a v).cycles = s.cycles := by
  unfold dmaWrite8IO
  simp only []
  repeat (first | simp [syncIo16_cycles, apuFifoPush_cycles] | split | rfl)

theorem dmaWrite8IO_regs (s : AGBState) (a : Nat) (v : UInt8) :
    (dmaWrite8IO s a v).regs = s.regs := by
  unfold dmaWrite8IO
  simp only []
  repeat (first | simp [syncIo16_regs, apuFifoPush_regs] | split | rfl)

theorem dmaWrite8IO_rom (s : AGBState) (a : Nat) (v : UInt8) :
    (dmaWrite8IO s a v).rom = s.rom := by
  unfold dmaWrite8IO
  simp only []
  repeat (first | simp [syncIo16_rom, apuFifoPush_rom] | split | rfl)

theorem dmaWrite8Nat_cycles (s : AGBState) (a : Nat) (v : UInt8) :
    (dmaWrite8Nat s a v).cycles = s.cycles := by
  unfold dmaWrite8Nat
  repeat (first | split | simp only [] | simp [saveWrite8_cycles, dmaWrite8IO_cycles] | rfl)

theorem dmaWrite8Nat_regs (s : AGBState) (a : Nat) (v : UInt8) :
    (dmaWrite8Nat s a v).regs = s.regs := by
  unfold dmaWrite8Nat
  repeat (first | split | simp only [] | simp [saveWrite8_regs, dmaWrite8IO_regs] | rfl)

theorem dmaWrite8Nat_rom (s : AGBState) (a : Nat) (v : UInt8) :
    (dmaWrite8Nat s a v).rom = s.rom := by
  unfold dmaWrite8Nat
  repeat (first | split | simp [saveWrite8_rom, dmaWrite8IO_rom] | rfl)

theorem dmaWrite8_cycles (s : AGBState) (addr : UInt32) (v : UInt8) :
    (dmaWrite8 s addr v).cycles = s.cycles := by
  unfold dmaWrite8
  exact dmaWrite8Nat_cycles s addr.toNat v

theorem dmaWrite8_regs (s : AGBState) (addr : UInt32) (v : UInt8) :
    (dmaWrite8 s addr v).regs = s.regs := by
  unfold dmaWrite8
  exact dmaWrite8Nat_regs s addr.toNat v

theorem dmaWrite8_rom (s : AGBState) (addr : UInt32) (v : UInt8) :
    (dmaWrite8 s addr v).rom = s.rom := by
  unfold dmaWrite8
  exact dmaWrite8Nat_rom s addr.toNat v

theorem dmaWrite16_cycles (s : AGBState) (addr : UInt32) (v : UInt16) :
    (dmaWrite16 s addr v).cycles = s.cycles := by
  unfold dmaWrite16
  rw [dmaWrite8_cycles, dmaWrite8_cycles]

theorem dmaWrite16_regs (s : AGBState) (addr : UInt32) (v : UInt16) :
    (dmaWrite16 s addr v).regs = s.regs := by
  unfold dmaWrite16
  rw [dmaWrite8_regs, dmaWrite8_regs]

theorem dmaWrite16_rom (s : AGBState) (addr : UInt32) (v : UInt16) :
    (dmaWrite16 s addr v).rom = s.rom := by
  unfold dmaWrite16
  rw [dmaWrite8_rom, dmaWrite8_rom]

theorem dmaWrite32_cycles (s : AGBState) (addr : UInt32) (v : UInt32) :
    (dmaWrite32 s addr v).cycles = s.cycles := by
  unfold dmaWrite32
  rw [dmaWrite16_cycles, dmaWrite16_cycles]

theorem dmaWrite32_regs (s : AGBState) (addr : UInt32) (v : UInt32) :
    (dmaWrite32 s addr v).regs = s.regs := by
  unfold dmaWrite32
  rw [dmaWrite16_regs, dmaWrite16_regs]

theorem dmaWrite32_rom (s : AGBState) (addr : UInt32) (v : UInt32) :
    (dmaWrite32 s addr v).rom = s.rom := by
  unfold dmaWrite32
  rw [dmaWrite16_rom, dmaWrite16_rom]

theorem dmaStep_cycles (s : AGBState) (src dst : UInt32) (is32 : Bool) :
    (dmaStep s src dst is32).cycles = s.cycles := by
  unfold dmaStep
  split
  · exact dmaWrite32_cycles _ _ _
  · exact dmaWrite16_cycles _ _ _

theorem dmaStep_regs (s : AGBState) (src dst : UInt32) (is32 : Bool) :
    (dmaStep s src dst is32).regs = s.regs := by
  unfold dmaStep
  split
  · exact dmaWrite32_regs _ _ _
  · exact dmaWrite16_regs _ _ _

theorem dmaStep_rom (s : AGBState) (src dst : UInt32) (is32 : Bool) :
    (dmaStep s src dst is32).rom = s.rom := by
  unfold dmaStep
  split
  · exact dmaWrite32_rom _ _ _
  · exact dmaWrite16_rom _ _ _

theorem dmaCopy_cycles (s : AGBState) (src dst : UInt32) (fuel : Nat)
    (is32 : Bool) (sstep dstep : Int) :
    (dmaCopy s src dst fuel is32 sstep dstep).cycles = s.cycles := by
  induction fuel generalizing s src dst with
  | zero => rfl
  | succ fuel ih =>
    simp only [dmaCopy]
    rw [ih]
    exact dmaStep_cycles _ _ _ _

theorem dmaCopy_regs (s : AGBState) (src dst : UInt32) (fuel : Nat)
    (is32 : Bool) (sstep dstep : Int) :
    (dmaCopy s src dst fuel is32 sstep dstep).regs = s.regs := by
  induction fuel generalizing s src dst with
  | zero => rfl
  | succ fuel ih =>
    simp only [dmaCopy]
    rw [ih]
    exact dmaStep_regs _ _ _ _

theorem dmaCopy_rom (s : AGBState) (src dst : UInt32) (fuel : Nat)
    (is32 : Bool) (sstep dstep : Int) :
    (dmaCopy s src dst fuel is32 sstep dstep).rom = s.rom := by
  induction fuel generalizing s src dst with
  | zero => rfl
  | succ fuel ih =>
    simp only [dmaCopy]
    rw [ih]
    exact dmaStep_rom _ _ _ _

theorem dmaBulk_some_cycles (s s' : AGBState) (src dst : UInt32) (total : Nat)
    (h : dmaBulk s src dst total = some s') : s'.cycles = s.cycles := by
  unfold dmaBulk at h
  split at h
  all_goals (first | simp at h | skip)
  all_goals (first | (obtain ⟨_, h2⟩ := h; subst h2; simp [withEwram_cycles, withIwram_cycles, withPal_cycles, withVram_cycles, withOam_cycles]) | (subst h; simp [withEwram_cycles, withIwram_cycles, withPal_cycles, withVram_cycles, withOam_cycles]))

theorem dmaBulk_some_regs (s s' : AGBState) (src dst : UInt32) (total : Nat)
    (h : dmaBulk s src dst total = some s') : s'.regs = s.regs := by
  unfold dmaBulk at h
  split at h
  all_goals (first | simp at h | skip)
  all_goals (first | (obtain ⟨_, h2⟩ := h; subst h2; simp [withEwram_regs, withIwram_regs, withPal_regs, withVram_regs, withOam_regs]) | (subst h; simp [withEwram_regs, withIwram_regs, withPal_regs, withVram_regs, withOam_regs]))

theorem dmaBulk_some_rom (s s' : AGBState) (src dst : UInt32) (total : Nat)
    (h : dmaBulk s src dst total = some s') : s'.rom = s.rom := by
  unfold dmaBulk at h
  split at h
  all_goals (first | simp at h | skip)
  all_goals (first | (obtain ⟨_, h2⟩ := h; subst h2; simp [withEwram_rom, withIwram_rom, withPal_rom, withVram_rom, withOam_rom]) | (subst h; simp [withEwram_rom, withIwram_rom, withPal_rom, withVram_rom, withOam_rom]))

theorem dmaRun_cycles (s : AGBState) (src dst : UInt32) (count : Nat) (is32 : Bool)
    (sstep dstep : Int) (unit : Nat) :
    (dmaRun s src dst count is32 sstep dstep unit).cycles = s.cycles := by
  unfold dmaRun
  split
  · cases hbulk : dmaBulk s src dst (count * unit) with
    | none => exact dmaCopy_cycles s src dst count is32 sstep dstep
    | some s1 => exact dmaBulk_some_cycles s s1 src dst _ hbulk
  · exact dmaCopy_cycles s src dst count is32 sstep dstep

theorem dmaRun_regs (s : AGBState) (src dst : UInt32) (count : Nat) (is32 : Bool)
    (sstep dstep : Int) (unit : Nat) :
    (dmaRun s src dst count is32 sstep dstep unit).regs = s.regs := by
  unfold dmaRun
  split
  · cases hbulk : dmaBulk s src dst (count * unit) with
    | none => exact dmaCopy_regs s src dst count is32 sstep dstep
    | some s1 => exact dmaBulk_some_regs s s1 src dst _ hbulk
  · exact dmaCopy_regs s src dst count is32 sstep dstep

theorem dmaRun_rom (s : AGBState) (src dst : UInt32) (count : Nat) (is32 : Bool)
    (sstep dstep : Int) (unit : Nat) :
    (dmaRun s src dst count is32 sstep dstep unit).rom = s.rom := by
  unfold dmaRun
  split
  · cases hbulk : dmaBulk s src dst (count * unit) with
    | none => exact dmaCopy_rom s src dst count is32 sstep dstep
    | some s1 => exact dmaBulk_some_rom s s1 src dst _ hbulk
  · exact dmaCopy_rom s src dst count is32 sstep dstep

theorem doDma_cycles (s : AGBState) (ch : Nat) :
    (doDma s ch).cycles = s.cycles := by
  unfold doDma
  repeat (first | simp [dmaRun_cycles] | split | rfl)

theorem doDma_regs (s : AGBState) (ch : Nat) :
    (doDma s ch).regs = s.regs := by
  unfold doDma
  repeat (first | simp [dmaRun_regs] | split | rfl)

theorem doDma_rom (s : AGBState) (ch : Nat) :
    (doDma s ch).rom = s.rom := by
  unfold doDma
  repeat (first | simp [dmaRun_rom] | split | rfl)

theorem fireDmaCh_cycles (s : AGBState) (old : AgbDma) (ch : Nat) :
    (fireDmaCh s old ch).cycles = s.cycles := by
  unfold fireDmaCh
  simp only []
  repeat (first | simp [doDma_cycles] | split | rfl)

theorem fireDmaCh_regs (s : AGBState) (old : AgbDma) (ch : Nat) :
    (fireDmaCh s old ch).regs = s.regs := by
  unfold fireDmaCh
  simp only []
  repeat (first | simp [doDma_regs] | split | rfl)

theorem fireDmaCh_rom (s : AGBState) (old : AgbDma) (ch : Nat) :
    (fireDmaCh s old ch).rom = s.rom := by
  unfold fireDmaCh
  simp only []
  repeat (first | simp [doDma_rom] | split | rfl)

theorem runVBlankCh_cycles (s : AGBState) (ch : Nat) :
    (runVBlankCh s ch).cycles = s.cycles := by
  unfold runVBlankCh
  simp only []
  repeat (first | simp [doDma_cycles] | split | rfl)

theorem runVBlankCh_regs (s : AGBState) (ch : Nat) :
    (runVBlankCh s ch).regs = s.regs := by
  unfold runVBlankCh
  simp only []
  repeat (first | simp [doDma_regs] | split | rfl)

theorem runVBlankCh_rom (s : AGBState) (ch : Nat) :
    (runVBlankCh s ch).rom = s.rom := by
  unfold runVBlankCh
  simp only []
  repeat (first | simp [doDma_rom] | split | rfl)

theorem runVBlankDma_cycles (s : AGBState) :
    (runVBlankDma s).cycles = s.cycles := by
  simp [runVBlankDma, runVBlankCh_cycles]

theorem runVBlankDma_regs (s : AGBState) :
    (runVBlankDma s).regs = s.regs := by
  simp [runVBlankDma, runVBlankCh_regs]

theorem runVBlankDma_rom (s : AGBState) :
    (runVBlankDma s).rom = s.rom := by
  simp [runVBlankDma, runVBlankCh_rom]

-- ── Cascade-timer preservation ──

theorem stepTimerCh_cycles (s : AGBState) (i n tin : Nat) :
    ((stepTimerCh s i n tin).1).cycles = s.cycles := by
  unfold stepTimerCh
  simp only []
  repeat (first | split | rfl)

-- ── Serial-window reads preserve everything but backup media ──

theorem memRead8E_cycles (s : AGBState) (addr : UInt32) :
    ((memRead8E s addr).1).cycles = s.cycles := by
  unfold memRead8E
  simp only []
  repeat (first | split | rfl)

theorem memRead8E_regs (s : AGBState) (addr : UInt32) :
    ((memRead8E s addr).1).regs = s.regs := by
  unfold memRead8E
  simp only []
  repeat (first | split | rfl)

theorem memRead8E_rom (s : AGBState) (addr : UInt32) :
    ((memRead8E s addr).1).rom = s.rom := by
  unfold memRead8E
  simp only []
  repeat (first | split | rfl)

theorem memRead16E_cycles (s : AGBState) (addr : UInt32) :
    ((memRead16E s addr).1).cycles = s.cycles := by
  unfold memRead16E
  simp only []
  repeat (first | simp [memRead8E_cycles] | split | rfl)

theorem memRead16E_regs (s : AGBState) (addr : UInt32) :
    ((memRead16E s addr).1).regs = s.regs := by
  unfold memRead16E
  simp only []
  repeat (first | simp [memRead8E_regs] | split | rfl)

theorem memRead16E_rom (s : AGBState) (addr : UInt32) :
    ((memRead16E s addr).1).rom = s.rom := by
  unfold memRead16E
  simp only []
  repeat (first | simp [memRead8E_rom] | split | rfl)

theorem memRead32E_cycles (s : AGBState) (addr : UInt32) :
    ((memRead32E s addr).1).cycles = s.cycles := by
  unfold memRead32E
  simp only []
  repeat (first | simp [memRead8E_cycles] | split | rfl)

theorem memRead32E_regs (s : AGBState) (addr : UInt32) :
    ((memRead32E s addr).1).regs = s.regs := by
  unfold memRead32E
  simp only []
  repeat (first | simp [memRead8E_regs] | split | rfl)

theorem memRead32E_rom (s : AGBState) (addr : UInt32) :
    ((memRead32E s addr).1).rom = s.rom := by
  unfold memRead32E
  simp only []
  repeat (first | simp [memRead8E_rom] | split | rfl)

theorem memWrite8_cycles (s : AGBState) (addr : UInt32) (v : UInt8) :
    (memWrite8 s addr v).cycles = s.cycles := by
  unfold memWrite8
  exact memWrite8Nat_cycles s addr.toNat v

theorem memWrite8_regs (s : AGBState) (addr : UInt32) (v : UInt8) :
    (memWrite8 s addr v).regs = s.regs := by
  unfold memWrite8
  exact memWrite8Nat_regs s addr.toNat v

theorem memWrite8_rom (s : AGBState) (addr : UInt32) (v : UInt8) :
    (memWrite8 s addr v).rom = s.rom := by
  unfold memWrite8
  exact memWrite8Nat_rom s addr.toNat v

-- NOTE: byte writes to timer reload/ctrl lanes now sync structs, so the
-- old `memWrite8_timers` preservation no longer holds (by design).

-- ── PPU non-interference (helpers preserve the PPU struct) ──

theorem saveWrite8_ppu (s : AGBState) (off : Nat) (v : UInt8) :
    (saveWrite8 s off v).ppu = s.ppu := by
  unfold saveWrite8
  simp only []
  repeat (first | split | rfl)

-- NOTE: bulk writes legitimately update PPU structs (Phase 9 fix for
-- stale video registers), so there are no unconditional `ppu`
-- preservation lemmas past `dmaWrite`. BG write theorems below evaluate
-- the whole chain on concrete addresses instead.
theorem syncDmaCh_ppu (s : AGBState) (idx base a : Nat) (v : UInt16) :
    (syncDmaCh s idx base a v).ppu = s.ppu := by
  unfold syncDmaCh
  simp only []
  repeat (first | split | rfl)

theorem syncDma16_ppu (s : AGBState) (a : Nat) (v : UInt16) :
    (syncDma16 s a v).ppu = s.ppu := by
  simp [syncDma16, syncDmaCh_ppu]

theorem syncTimer16_ppu (s : AGBState) (a : Nat) (v : UInt16) :
    (syncTimer16 s a v).ppu = s.ppu := by
  unfold syncTimer16 syncTimerReload syncTimerCtrl
  simp only []
  repeat (first | split | rfl)

-- ── BG register write semantics ──

theorem setLane4_get0 (a : Array UInt16) (v : UInt16) :
    (setLane4 a 0 v).getD 0 0 = v := by
  simp [setLane4]

theorem bgcnt0_write (s : AGBState) (v : UInt16) :
    (memWrite16 s 0x04000008 v).ppu.bgcnt.getD 0 0 = v := by
  simp [memWrite16, memWrite16IO, isSyncLane16, syncIo16, syncBg16, syncBgCnt, syncBgHo, syncBgVo,
    setLane4, syncBld16, syncTimer16_ppu, syncDma16_ppu, syncApu16_ppu]

theorem bghofs0_write (s : AGBState) (v : UInt16) :
    (memWrite16 s 0x04000010 v).ppu.bghofs.getD 0 0 = v := by
  simp [memWrite16, memWrite16IO, isSyncLane16, syncIo16, syncBg16, syncBgCnt, syncBgHo, syncBgVo,
    setLane4, syncBld16, syncTimer16_ppu, syncDma16_ppu, syncApu16_ppu]

theorem memWrite16Snd_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (memWrite16Snd s a v).cycles = s.cycles := by
  unfold memWrite16Snd
  simp only []
  repeat (first | simp [apuFifoPush_cycles] | split | rfl)

theorem memWrite16Snd_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (memWrite16Snd s a v).regs = s.regs := by
  unfold memWrite16Snd
  simp only []
  repeat (first | simp [apuFifoPush_regs] | split | rfl)

theorem memWrite16Snd_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (memWrite16Snd s a v).rom = s.rom := by
  unfold memWrite16Snd
  simp only []
  repeat (first | simp [apuFifoPush_rom] | split | rfl)

theorem memWrite16IO_cycles (s : AGBState) (a : Nat) (v : UInt16) :
    (memWrite16IO s a v).cycles = s.cycles := by
  unfold memWrite16IO
  repeat (first | split | simp only [] | simp [syncIo16_cycles, fireDmaCh_cycles, memWrite16Snd_cycles] | rfl)

theorem memWrite16IO_regs (s : AGBState) (a : Nat) (v : UInt16) :
    (memWrite16IO s a v).regs = s.regs := by
  unfold memWrite16IO
  repeat (first | split | simp only [] | simp [syncIo16_regs, fireDmaCh_regs, memWrite16Snd_regs] | rfl)

theorem memWrite16IO_rom (s : AGBState) (a : Nat) (v : UInt16) :
    (memWrite16IO s a v).rom = s.rom := by
  unfold memWrite16IO
  repeat (first | split | simp only [] | simp [syncIo16_rom, fireDmaCh_rom, memWrite16Snd_rom] | rfl)

theorem memWrite16_cycles (s : AGBState) (addr : UInt32) (v : UInt16) :
    (memWrite16 s addr v).cycles = s.cycles := by
  unfold memWrite16
  split
  · exact memWrite16IO_cycles s addr.toNat v
  · rw [memWrite8_cycles, memWrite8_cycles]

theorem memWrite16_regs (s : AGBState) (addr : UInt32) (v : UInt16) :
    (memWrite16 s addr v).regs = s.regs := by
  unfold memWrite16
  split
  · exact memWrite16IO_regs s addr.toNat v
  · rw [memWrite8_regs, memWrite8_regs]

theorem memWrite16_rom (s : AGBState) (addr : UInt32) (v : UInt16) :
    (memWrite16 s addr v).rom = s.rom := by
  unfold memWrite16
  split
  · exact memWrite16IO_rom s addr.toNat v
  · rw [memWrite8_rom, memWrite8_rom]

theorem memWrite32_cycles (s : AGBState) (addr : UInt32) (v : UInt32) :
    (memWrite32 s addr v).cycles = s.cycles := by
  unfold memWrite32
  simp only []
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [memWrite16_cycles, memWrite16_cycles]

theorem memWrite32_regs (s : AGBState) (addr : UInt32) (v : UInt32) :
    (memWrite32 s addr v).regs = s.regs := by
  unfold memWrite32
  simp only []
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [memWrite16_regs, memWrite16_regs]

-- ── IRQ register semantics ──

theorem ie_write (s : AGBState) (addr : UInt32) (h : addr.toNat = 0x04000200) (v : UInt16) :
    (memWrite16 s addr v).irq.ie = v := by
  simp [memWrite16, memWrite16IO, isSyncLane16, h]

theorem if_write_clears (s : AGBState) (addr : UInt32) (h : addr.toNat = 0x04000202)
    (v : UInt16) :
    (memWrite16 s addr v).irq.if_ = s.irq.if_ &&& ~~~v := by
  simp [memWrite16, memWrite16IO, isSyncLane16, h]

theorem ime_write (s : AGBState) (addr : UInt32) (h : addr.toNat = 0x04000208)
    (v : UInt16) :
    (memWrite16 s addr v).irq.ime = ((v &&& 1) != 0) := by
  simp [memWrite16, memWrite16IO, isSyncLane16, h]

theorem ime_write8 (s : AGBState) (addr : UInt32) (h : addr.toNat = 0x04000208)
    (v : UInt8) :
    (memWrite8 s addr v).irq.ime = ((v.toNat &&& 1) == 1) := by
  simp [memWrite8, memWrite8Nat, memWrite8IO, h]

-- ── Exact cycle accounting ──

theorem stepTimers_cycles (s : AGBState) (n : Nat) :
    (stepTimers s n).cycles = s.cycles := by
  unfold stepTimers
  simp only []
  repeat (first | split | rfl | simp only [apuTimerOverflow_cycles])

theorem stepPpu_cycles (s : AGBState) (n : Nat) :
    (stepPpu s n).cycles = s.cycles := by
  unfold stepPpu
  simp only []
  repeat (first | simp [runVBlankDma_cycles] | split | rfl)

theorem advanceOnRegs_cycles (s : AGBState) (regs1 : ArmRegs) (busVal : UInt32)
    (n : Nat) : (advanceOnRegs s regs1 busVal n).cycles = s.cycles + n := by
  unfold advanceOnRegs
  simp only []
  repeat (first | split | rfl | simp only [stepPpu_cycles, apuTimerOverflow_cycles])

theorem advance_cycles (s : AGBState) (n : Nat) :
    (advance s n).cycles = s.cycles + n := by
  unfold advance
  exact advanceOnRegs_cycles _ _ _ _

/-- Register writes never touch `cpsr` (fast arms thread flags purely). -/
theorem ArmRegs.set_cpsr (rs : ArmRegs) (i : Nat) (v : UInt32) :
    (rs.set i v).cpsr = rs.cpsr := by
  unfold ArmRegs.set
  simp only []
  repeat (first | split | rfl)

/-- Unsigned wrap-free step: small offsets off a windowed base. -/
theorem u32_add_toNat' (a : UInt32) (i n : Nat) (hi : i < n)
    (hwin : a.toNat + n ≤ 0x0E000000) : (a + w32 i).toNat = a.toNat + i := by
  have hi32 : (w32 i).toNat = i := by
    simp only [w32, UInt32.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [UInt32.toNat_add, hi32, Nat.mod_eq_of_lt (by omega)]



/-- Fast steps never go backwards in time (every arm ends in the
    fused tail; the fallthrough contradicts `some`). -/
theorem stepThumbFast_some_mono (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (s' : AGBState) (h : stepThumbFast s pc w hw = some s') :
    s.cycles ≤ s'.cycles := by
  unfold stepThumbFast at h
  split at h
  · obtain rfl := Option.some_inj.mp h
    rw [advanceOnRegs_cycles]
    exact Nat.le_add_right s.cycles _
  · simp at h

theorem serviceIrq_cycles (s : AGBState) : (serviceIrq s).cycles = s.cycles := by
  rfl

-- ── Fresh-state facts ──

theorem fresh_rom (rom : ByteArray) : (AGBState.fresh rom).rom = rom := by
  rfl

theorem fresh_pc (rom : ByteArray) : (AGBState.fresh rom).regs.pc = 0x08000000 := by
  rfl

theorem cpsrT_boot : cpsrT 0x3F = true := by decide

theorem fresh_thumb (rom : ByteArray) : cpsrT (AGBState.fresh rom).regs.cpsr = true := by
  have h : (AGBState.fresh rom).regs.cpsr = 0x3F := by rfl
  rw [h]; exact cpsrT_boot

theorem fresh_vcount (rom : ByteArray) : (AGBState.fresh rom).ppu.vcount = 0 := by
  rfl

theorem freshArm_pc (rom : ByteArray) (kind : SaveKind) :
    (AGBState.freshArmSave rom kind).regs.pc = 0x08000000 := by
  rfl

theorem cpsrT_arm_boot : cpsrT 0x1F = false := by decide

theorem cpsrMode_arm_boot : cpsrMode 0x1F = 0x1F := by decide

theorem freshArm_arm (rom : ByteArray) (kind : SaveKind) :
    cpsrT (AGBState.freshArmSave rom kind).regs.cpsr = false := by
  have h : (AGBState.freshArmSave rom kind).regs.cpsr = 0x1F := by rfl
  rw [h]; exact cpsrT_arm_boot

theorem freshArm_sys (rom : ByteArray) (kind : SaveKind) :
    cpsrMode (AGBState.freshArmSave rom kind).regs.cpsr = 0x1F := by
  have h : (AGBState.freshArmSave rom kind).regs.cpsr = 0x1F := by rfl
  rw [h]; exact cpsrMode_arm_boot

theorem bootIsArm_thumb_entry :
    bootIsArm (ByteArray.mk #[0x0B, 0x49, 0x1F, 0x20]) = false := by decide

theorem bootIsArm_arm_entry :
    bootIsArm (ByteArray.mk #[0x2E, 0x00, 0x00, 0xEA]) = true := by decide

theorem bootIsArm_empty : bootIsArm ByteArray.empty = false := by decide

theorem freshAuto_thumb_entry (kind : SaveKind) :
    cpsrT (AGBState.freshAuto (ByteArray.mk #[0x0B, 0x49, 0x1F, 0x20]) kind).regs.cpsr = true := by
  have h : bootIsArm (ByteArray.mk #[0x0B, 0x49, 0x1F, 0x20]) = false :=
    bootIsArm_thumb_entry
  unfold AGBState.freshAuto
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]
  have h2 : (AGBState.freshSave (ByteArray.mk #[0x0B, 0x49, 0x1F, 0x20]) kind).regs.cpsr = 0x3F := by rfl
  rw [h2]; exact cpsrT_boot

theorem freshAuto_arm_entry (kind : SaveKind) :
    cpsrT (AGBState.freshAuto (ByteArray.mk #[0x2E, 0x00, 0x00, 0xEA]) kind).regs.cpsr = false := by
  have h : bootIsArm (ByteArray.mk #[0x2E, 0x00, 0x00, 0xEA]) = true :=
    bootIsArm_arm_entry
  unfold AGBState.freshAuto
  rw [if_pos h]
  have h2 : (AGBState.freshArmSave (ByteArray.mk #[0x2E, 0x00, 0x00, 0xEA]) kind).regs.cpsr = 0x1F := by rfl
  rw [h2]; exact cpsrT_arm_boot

/-- Fetch scene: 8-byte ROM over the reset vector. -/
def fetchScene : AGBState :=
  { ({} : AGBState) with
    rom := ByteArray.mk #[0x0B, 0x49, 0x1F, 0x20, 0x78, 0x56, 0x34, 0x12] }

/-- Sliced low halfword equals the direct 16-bit fetch. -/
theorem fetchHw_lo :
    fetchHw (memRead32 fetchScene (0x08000000 &&& 0xFFFFFFFC)) 0x08000000
      = memRead16 fetchScene 0x08000000 := by decide

/-- Sliced high halfword equals the direct 16-bit fetch. -/
theorem fetchHw_hi :
    fetchHw (memRead32 fetchScene (0x08000002 &&& 0xFFFFFFFC)) 0x08000002
      = memRead16 fetchScene 0x08000002 := by decide

end AGB
