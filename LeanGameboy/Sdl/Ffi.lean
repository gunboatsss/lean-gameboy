/-
  LeanGameboy.Sdl.Ffi — `@[extern]` bindings to `c/shim.c`.

  The shim loads SDL2 with `dlopen` at runtime; every call is safe
  with no SDL present (`openWindow` then returns nonzero).
-/
namespace GB.Sdl

/-- Open a scaled window. Returns 0 on success, nonzero on failure. -/
@[extern "gb_open"]
opaque openWindow : UInt32 → IO UInt32

/-- Blit a 160×144×4-byte ARGB8888 (little-endian) frame. -/
@[extern "gb_blit"]
opaque blit : @& ByteArray → IO Unit

/-- Blit a 160×144 `Array UInt32` frame directly (no byte conversion). -/
@[extern "gb_blit32"]
opaque blit32 : @& Array UInt32 → IO Unit

/-- Present the current texture. -/
@[extern "gb_present"]
opaque present : IO Unit

/-- Poll input. Low 8 bits: Right Left Up Down A B Select Start
    (matches `JoypadState` field order); bit 8: quit requested. -/
@[extern "gb_poll"]
opaque poll : IO UInt32

/-- Queue S16LE mono audio samples (dropped when the queue is full). -/
@[extern "gb_audio"]
opaque audio : @& ByteArray → IO Unit

/-- Sleep `ms` milliseconds. -/
@[extern "gb_delay"]
opaque delayMs : UInt32 → IO Unit

/-- Milliseconds since SDL init (0 without SDL). -/
@[extern "gb_ticks"]
opaque ticksMs : IO UInt32

/-- Destroy the window / shut down SDL. -/
@[extern "gb_close"]
opaque close : IO Unit

end GB.Sdl
