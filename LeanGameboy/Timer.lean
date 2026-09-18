/-
  LeanGameboy.Timer — DIV / TIMA / TMA / TAC.

  Modelled after Pan Docs: a 16-bit internal counter advanced by 4
  per M-cycle; TIMA rises on the falling edge of
  `(selectedBit && tacEnabled)`.
-/
import LeanGameboy.Basic

namespace GB

/-- Timer registers + internal divider. -/
structure TimerState where
  divInternal : Nat := 0   -- 16-bit internal counter (masked to 0xFFFF)
  tima : UInt8 := 0
  tma : UInt8 := 0
  tac : UInt8 := 0
  prevAnd : Bool := false  -- previous value of (bit && enabled)
  irq : Bool := false      -- timer interrupt requested
deriving DecidableEq, Repr

namespace TimerState

/-- DIV as seen by the CPU (upper 8 bits of the internal counter). -/
def div (t : TimerState) : UInt8 :=
  w8 ((t.divInternal / 256) % 256)

/-- Which internal-counter bit clocks TIMA for the TAC frequency. -/
def freqBit (tac : UInt8) : Nat :=
  match tac.toNat % 4 with
  | 0 => 9 | 1 => 3 | 2 => 5 | _ => 7

/-- Current `(selectedBit && enabled)` level. -/
def andLevel (internal : Nat) (tac : UInt8) : Bool :=
  let bit := (internal >>> freqBit tac) % 2 == 1
  bit && (tac.toNat / 4) % 2 == 1

/-- Advance the timer by `dots` T-cycles in O(1).
    TIMA counts falling edges of the selected divider bit; edges in a
    batch are counted exactly with integer division, and overflow
    reloads TMA with an interrupt request. -/
def stepDots (t : TimerState) (dots : Nat) : TimerState :=
  if dots == 0 then t
  else
    let internal := (t.divInternal + dots) % 65536
    let enabled := (t.tac.toNat / 4) % 2 == 1
    if !enabled then
      { t with divInternal := internal, prevAnd := false }
    else
      let period := 1 <<< (freqBit t.tac + 1)
      let edges := ((t.divInternal + dots) / period) - (t.divInternal / period)
      -- apply `edges` TIMA increments with TMA reload on overflow
      let (tima', irq') :=
        if edges == 0 then (t.tima, t.irq)
        else if t.tima.toNat + edges < 256 then
          (w8 (t.tima.toNat + edges), t.irq)
        else
          let rest := edges - (256 - t.tima.toNat)
          (w8 ((t.tma.toNat + rest) % 256), true)
      { t with
        divInternal := internal
        tima := tima'
        prevAnd := andLevel internal t.tac
        irq := irq' }

/-- Advance the timer by `mCycles` M-cycles at single speed
    (1 M-cycle = 4 T-cycles). Double-speed callers use `stepDots`
    with 2 T-cycles per M-cycle instead. -/
def step (t : TimerState) (mCycles : Nat) : TimerState :=
  t.stepDots (mCycles * 4)

/-- Write to DIV: resets the internal counter (may clock TIMA). -/
def writeDiv (t : TimerState) : TimerState :=
  let lvl := andLevel 0 t.tac
  let (tima', irq') :=
    if t.prevAnd && !lvl then
      if t.tima == 0xFF then (t.tma, true) else (t.tima + 1, t.irq)
    else (t.tima, t.irq)
  { t with divInternal := 0, tima := tima', prevAnd := lvl, irq := irq' }

/-- Acknowledge the timer interrupt. -/
def ackIrq (t : TimerState) : TimerState :=
  { t with irq := false }

end TimerState

end GB
