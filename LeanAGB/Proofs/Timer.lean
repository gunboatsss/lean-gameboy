/-
  LeanAGB.Proofs.Timer — timer control semantics + edge instances.
  Disabled or count-up timers are frozen; enabled timers count with
  exact prescale division; overflow reloads and raises IF.3.
-/
import LeanAGB.Bus
import LeanAGB.Proofs.Apu

namespace AGB

-- ── Frozen when disabled (all four channels) ──

theorem stepTimerCh_disabled_eq (s : AGBState) (i n tin : Nat)
    (h : ((((s.timers.ch.getD i {}).ctrl >>> 7) &&& 1) == 0)) :
    stepTimerCh s i n tin = (s, 0) := by
  unfold stepTimerCh
  simp only []
  split
  · rfl
  · simp_all

theorem stepTimerChCore_disabled_eq (tmrs : AgbTimers) (irq : AgbIrq) (i n tin : Nat)
    (h : ((((tmrs.ch.getD i {}).ctrl >>> 7) &&& 1) == 0)) :
    stepTimerChCore tmrs irq i n tin = (tmrs, irq, 0) := by
  unfold stepTimerChCore
  simp only []
  split
  · rfl
  · simp_all

theorem timers_all_disabled_frozen (s : AGBState) (n : Nat)
    (h0 : ((((s.timers.ch.getD 0 {}).ctrl >>> 7) &&& 1) == 0))
    (h1 : ((((s.timers.ch.getD 1 {}).ctrl >>> 7) &&& 1) == 0))
    (h2 : ((((s.timers.ch.getD 2 {}).ctrl >>> 7) &&& 1) == 0))
    (h3 : ((((s.timers.ch.getD 3 {}).ctrl >>> 7) &&& 1) == 0)) :
    (stepTimers s n).timers = s.timers := by
  have e0 := stepTimerChCore_disabled_eq s.timers s.irq 0 n 0 h0
  have e1 := stepTimerChCore_disabled_eq s.timers s.irq 1 n 0 h1
  have e2 := stepTimerChCore_disabled_eq s.timers s.irq 2 n 0 h2
  have e3 := stepTimerChCore_disabled_eq s.timers s.irq 3 n 0 h3
  unfold stepTimers
  simp [e0, e1, e2, e3]

-- ── Cascade: count-up channels tick on lower overflow ──

/-- TM0 about to overflow, TM1 in count-up mode. -/
def timerCascade : AGBState :=
  { ({} : AGBState) with
    timers := { ch := #[{ reload := 0, cnt := 0xFFFF, ctrl := 0x80, acc := 0 },
      { reload := 0xBEEF, cnt := 0, ctrl := 0x84, acc := 0 }, {}, {}] } }

theorem timer_cascade_tick :
    ((stepTimers timerCascade 1).timers.ch.getD 1 {}).cnt = 1 := by
  decide

theorem timer_cascade_reload :
    ((stepTimers timerCascade 1).timers.ch.getD 0 {}).cnt = 0 := by
  decide

theorem timer_cascade_irq : (stepTimers timerCascade 1).irq.if_ = 0x08 := by
  decide

-- ── Prescaler table ──

theorem timerDiv_1 : timerDiv 0 = 1 := by decide
theorem timerDiv_64 : timerDiv 1 = 64 := by decide
theorem timerDiv_256 : timerDiv 2 = 256 := by decide
theorem timerDiv_1024 : timerDiv 3 = 1024 := by decide
theorem timerDiv_ctrl80 : timerDiv 0x80 = 1 := by decide

-- ── Edge instances (exact counting + overflow, kernel-checked) ──

/-- Timer 0 armed: reload 0xFF00, enabled, prescale /1. -/
def timerArmed : AGBState :=
  { ({} : AGBState) with
    timers := { ch := #[{ reload := 0xFF00, cnt := 0, ctrl := 0x80, acc := 0 }, {}, {}, {}] } }

theorem timer_counts_256 :
    ((stepTimers timerArmed 256).timers.ch.getD 0 {}).cnt = 256 := by
  decide

theorem timer_counts_acc :
    ((stepTimers timerArmed 100).timers.ch.getD 0 {}).cnt = 100 := by
  decide

/-- Overflow: 0xFFFF + 1 tick reloads and raises IF.3. -/
def timerFull : AGBState :=
  { ({} : AGBState) with
    timers := { ch := #[{ reload := 0x1234, cnt := 0xFFFF, ctrl := 0x80, acc := 0 }, {}, {}, {}] } }

theorem timer_overflow_reloads :
    ((stepTimers timerFull 1).timers.ch.getD 0 {}).cnt = 0x1234 := by
  decide

theorem timer_overflow_irq : (stepTimers timerFull 1).irq.if_ = 8 := by
  decide

-- ── Halt-jump bounds (kernel-checked instances) ──

theorem timerOverBoundCh_disabled : timerOverBoundCh {} 0 = 0 := by decide

theorem timerOverBoundCh_countup :
    timerOverBoundCh { ctrl := 0x84, cnt := 0, acc := 0 } 1 = 0 := by decide

theorem timerOverBoundCh_full_rate :
    timerOverBoundCh { reload := 0, cnt := 0, ctrl := 0x80, acc := 0 } 0
      = 0x10000 := by decide

theorem timerOverBoundCh_prescale :
    timerOverBoundCh { reload := 0, cnt := 0, ctrl := 0x81, acc := 0 } 0
      = 0x10000 * 64 := by decide

theorem timerOverBoundCh_debt :
    timerOverBoundCh { reload := 0, cnt := 0xFF00, ctrl := 0x80, acc := 0 } 0
      = 0x100 := by decide

/-- The clamp always makes progress. -/
theorem jumpClamp_pos (m : Nat) : 1 <= jumpClamp m := by
  unfold jumpClamp
  split <;> omega

/-- The jump always makes progress. -/
theorem haltJump_pos (s : AGBState) : 1 <= haltJump s := by
  unfold haltJump
  exact jumpClamp_pos _

/-- Wake path agrees with `stepCPU` exactly (same wake check, same
    service/unhalt, same 3/1-cycle charge). -/
theorem stepHaltJump_parked (s : AGBState) (hh : s.halted = true)
    (hw : haltWake s = true) : stepHaltJump s = stepCPU s := by
  simp [stepHaltJump, stepCPU, hh, hw]

/-- Unit jump agrees with `stepCPU` (no wake, distance 1). -/
theorem stepHaltJump_single (s : AGBState) (hh : s.halted = true)
    (hw : haltWake s = false) (hj : haltJump s = 1) :
    stepHaltJump s = stepCPU s := by
  simp [stepHaltJump, stepCPU, hh, hw, hj]

end AGB
