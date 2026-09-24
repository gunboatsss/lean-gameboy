/-
  LeanAGB.Sdl.Ffi — `@[extern]` bindings to `c/shim.c` (240×160 path).

  The shim loads SDL2 with `dlopen` at runtime; every call is safe
  with no SDL present (`openWindow` then returns nonzero).
-/
namespace AGB.Sdl

/-- Open a scaled 240×160 window. Returns 0 on success, nonzero on failure. -/
@[extern "agb_open"]
opaque openWindow : UInt32 → IO UInt32

/-- Blit a 240×160 `Array UInt32` frame directly (no byte conversion). -/
@[extern "agb_blit32"]
opaque blit32 : @& Array UInt32 → IO Unit

/-- Present the current texture. -/
@[extern "agb_present"]
opaque present : IO Unit

/-- Queue S16LE stereo audio samples at 32768 Hz (dropped when the
    queue is full; no-op without an audio device). -/
@[extern "agb_audio"]
opaque audioPush : @& ByteArray → IO Unit

/-- Queued-but-unplayed audio bytes (0 without an audio device).
    Drives audio-clock pacing: catch up when low, coast when high. -/
@[extern "agb_queued"]
opaque audioQueued : IO UInt32

/-- Poll input. Low 8 bits: Right Left Up Down A B Select Start
    (same order as the DMG shim); bit 8: quit requested;
    bit 10: L (Q), bit 11: R (W). -/
@[extern "gb_poll"]
opaque poll : IO UInt32

/-- Sleep `ms` milliseconds. -/
@[extern "gb_delay"]
opaque delayMs : UInt32 → IO Unit

/-- Milliseconds since SDL init (0 without SDL). -/
@[extern "gb_ticks"]
opaque ticksMs : IO UInt32

/-- Destroy the window / shut down SDL. -/
@[extern "agb_close"]
opaque close : IO Unit

end AGB.Sdl
