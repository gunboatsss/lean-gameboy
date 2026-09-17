/-
  LeanGameboy.Cpu.Regs — LR35902 (SM83) registers and flags.

  Flags are stored as separate `Bool`s (rather than packed bits) so
  per-instruction flag theorems stay simple. Packing helpers convert
  to/from the architectural AF representation.
-/
import LeanGameboy.Basic

namespace GB

/-- CPU registers plus interrupt/halt bookkeeping. -/
structure Regs where
  a : UInt8 := 0
  b : UInt8 := 0
  c : UInt8 := 0
  d : UInt8 := 0
  e : UInt8 := 0
  h : UInt8 := 0
  l : UInt8 := 0
  sp : UInt16 := 0
  pc : UInt16 := 0
  -- flags: Z N H C
  z : Bool := false
  n : Bool := false
  hf : Bool := false
  cf : Bool := false
  -- interrupt master enable + delayed EI effect
  ime : Bool := false
  eiDelay : Bool := false
  halted : Bool := false
deriving DecidableEq, Repr

namespace Regs

/-- Post-boot DMG defaults (boot ROM skipped). -/
def bootDefaults : Regs :=
  { a := 0x01, b := 0x00, c := 0x13, d := 0x00, e := 0xD8,
    h := 0x01, l := 0x4D, sp := 0xFFFE, pc := 0x0100,
    z := true, n := false, hf := true, cf := true }

/-- BC pair. -/
def bc (r : Regs) : UInt16 := join16 r.b r.c
/-- DE pair. -/
def de (r : Regs) : UInt16 := join16 r.d r.e
/-- HL pair. -/
def hl (r : Regs) : UInt16 := join16 r.h r.l
/-- AF pair (low nibble of F is always 0 on hardware). -/
def af (r : Regs) : UInt16 :=
  let f : UInt8 :=
    (if r.z then 0x80 else 0x00) |||
    (if r.n then 0x40 else 0x00) |||
    (if r.hf then 0x20 else 0x00) |||
    (if r.cf then 0x10 else 0x00)
  join16 r.a f

/-- Split a word into the BC pair. -/
def setBC (r : Regs) (v : UInt16) : Regs :=
  { r with b := hiByte v, c := loByte v }
/-- Split a word into the DE pair. -/
def setDE (r : Regs) (v : UInt16) : Regs :=
  { r with d := hiByte v, e := loByte v }
/-- Split a word into the HL pair. -/
def setHL (r : Regs) (v : UInt16) : Regs :=
  { r with h := hiByte v, l := loByte v }
/-- Split a word into A + flags. -/
def setAF (r : Regs) (v : UInt16) : Regs :=
  let f := loByte v
  { a := hiByte v, b := r.b, c := r.c, d := r.d, e := r.e,
    h := r.h, l := r.l, sp := r.sp, pc := r.pc,
    z := bitGet f 7, n := bitGet f 6, hf := bitGet f 5, cf := bitGet f 4,
    ime := r.ime, eiDelay := r.eiDelay, halted := r.halted }

end Regs

end GB
