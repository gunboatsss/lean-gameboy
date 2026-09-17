/-
  LeanGameboy.Sdl.Driver — pure-Lean glue between `GBState` and the
  SDL shim: pixel/audio conversion, input mapping, frame pacing.
-/
import LeanGameboy.Emu
import LeanGameboy.Sdl.Ffi

namespace GB.Sdl

/-- Map a poll bitmask onto button state (keeps P1 select bits). -/
def buttonsOf (cur : JoypadState) (mask : UInt32) : JoypadState :=
  let t (b : Nat) : Bool := ((mask >>> b.toUInt32).toNat) % 2 == 1
  { cur with
    right := t 0
    left := t 1
    up := t 2
    down := t 3
    a := t 4
    b := t 5
    select := t 6
    start := t 7 }

/-- Present one frame + push audio. Returns possibly-drained state. -/
def presentFrame (s : GBState) (mute : Bool) : IO GBState := do
  blit32 s.fb
  let s ←
  if !mute then
    let (apu, xs) := s.apu.drain
    let s := { s with apu := apu }
    if xs.size == 0 then pure s
    else do
      audio xs
      pure s
    else pure { s with apu := (s.apu.drain).1 }
  present
  pure s

/-- Target frame period: 70224 dots at 4194304 Hz ≈ 16.74 ms. -/
def frameMs : UInt32 := 17

end GB.Sdl
