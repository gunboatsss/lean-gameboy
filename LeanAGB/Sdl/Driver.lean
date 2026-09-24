/-
  LeanAGB.Sdl.Driver — pure-Lean glue between `AGBState` and the SDL
  shim: input mapping, KEYCNT interrupt, frame pacing. Audio pushes
  32768 Hz stereo s16 per presented frame (`agb_audio`); without an
  audio device pushes are no-ops.
-/
import LeanAGB.Emu
import LeanAGB.Sdl.Ffi

namespace AGB.Sdl

open AGB

/-- Poll mask (shim order R L U D A B Sel Sta, plus 10 = L (Q key),
    11 = R (W key)) → KEYINPUT bits (A B Sel Sta Right Left Up Down
    R L); released reads 1. -/
def buttonsToInput (mask : UInt32) : UInt16 :=
  let t (b : Nat) : Bool := ((mask.toNat >>> b) &&& 1) == 1
  let bit (held : Bool) : Nat := if held then 0 else 1
  w16 (bit (t 4) * 1 + bit (t 5) * 2 + bit (t 6) * 4 + bit (t 7) * 8
    + bit (t 0) * 16 + bit (t 1) * 32 + bit (t 2) * 64 + bit (t 3) * 128
    + bit (t 11) * 256 + bit (t 10) * 512)

/-- Apply host buttons: refresh KEYINPUT, raise IF.12 on KEYCNT match. -/
def setButtons (s : AGBState) (mask : UInt32) : AGBState :=
  let key := { s.key with input := buttonsToInput mask }
  let irq := if keyIrqFire key.input key.cnt then
      { s.irq with if_ := s.irq.if_ ||| (0x1000 : UInt16) }
    else s.irq
  { s with key := key, irq := irq }

/-- Present one emulated frame (refreshes `fb` through the render
    memo first; F1 snapshots bypass the memo via `dumpPPM`). -/
def presentAgbFrame (s : AGBState) (m : RenderMemo) :
    IO (AGBState × RenderMemo) := do
  let (s, m) := memoRenderFrame s m
  blit32 s.fb
  present
  pure (s, m)

/-- Target frame period: 280896 dots at 16.78 MHz ≈ 16.74 ms
    (exactly 4× the DMG clock, same pacing constants). -/
def frameMsBase : Nat := 16
def frameMsFracStep : Nat := 48674
def frameMsFracMod : Nat := 65536

/-- Advance the fractional frame deadline. Returns `(due, frac')`. -/
def nextDeadline (nextDue frac : Nat) : Nat × Nat :=
  let f := frac + frameMsFracStep
  (nextDue + frameMsBase + f / frameMsFracMod, f % frameMsFracMod)

end AGB.Sdl
