/-
  LeanAGB.Basic — pure helpers for the GBA (ARM7TDMI) core.
  Mirrors LeanGameboy.Basic style; AGB namespace to avoid clashes.
-/
namespace AGB

/-- Wrap a natural into a 32-bit word. -/
def w32 (n : Nat) : UInt32 := UInt32.ofNat n

/-- Wrap a natural into a 16-bit halfword. -/
def w16 (n : Nat) : UInt16 := UInt16.ofNat n

/-- Wrap a natural into a byte. -/
def w8 (n : Nat) : UInt8 := UInt8.ofNat n

/-- Rotate right a 32-bit value (ARM barrel-shifter primitive). -/
def rotr32 (x : UInt32) (n : Nat) : UInt32 :=
  let s := n % 32
  if s == 0 then x else (x >>> s.toUInt32) ||| (x <<< ((32 - s).toUInt32))

/-- Sign-extend an `n`-bit field (value in low bits of a Nat). -/
def signExt (val bits : Nat) : Int :=
  let v := val % (1 <<< bits)
  if v < (1 <<< (bits - 1)) then (v : Int) else (v : Int) - (1 <<< bits)

/-- Test bit `i` of a 32-bit word. -/
def bitGet32 (x : UInt32) (i : Nat) : Bool :=
  ((x >>> i.toUInt32) &&& 1) != 0

/-- Set bit `i` of a 32-bit word. -/
def bitSet32 (x : UInt32) (i : Nat) : UInt32 :=
  x ||| (1 <<< i.toUInt32)

/-- Clear bit `i` of a 32-bit word. -/
def bitClear32 (x : UInt32) (i : Nat) : UInt32 :=
  x &&& ~~~(1 <<< i.toUInt32)

/-- 15-bit BGR555 → 32-bit ARGB8888 (reuse CGB output convention). -/
def bgr555ToARGB (c : UInt16) : UInt32 :=
  let r := ((c.toUInt32 >>> 0) &&& 0x1F) * 255 / 31
  let g := ((c.toUInt32 >>> 5) &&& 0x1F) * 255 / 31
  let b := ((c.toUInt32 >>> 10) &&& 0x1F) * 255 / 31
  (0xFF : UInt32) <<< 24 ||| (r <<< 16) ||| (g <<< 8) ||| b

/-- Read a byte from a `ByteArray`, 0xFF out of bounds (open-bus-ish). -/
@[inline] def bget (b : ByteArray) (addr : Nat) : UInt8 :=
  if h : addr < b.size then b[addr]'h else 0xFF

/-- Write a byte into a `ByteArray`, no-op out of bounds. -/
def bset (b : ByteArray) (addr : Nat) (v : UInt8) : ByteArray :=
  if addr < b.size then b.set! addr v else b

/-- Little-endian 16-bit read over a `ByteArray`. -/
@[inline] def bget16LE (b : ByteArray) (addr : Nat) : UInt16 :=
  let lo := (bget b addr).toUInt16
  let hi := (bget b (addr + 1)).toUInt16
  (hi <<< 8) ||| lo

/-- Little-endian 32-bit read over a `ByteArray`. -/
def bget32LE (b : ByteArray) (addr : Nat) : UInt32 :=
  let b0 := (bget b addr).toUInt32
  let b1 := (bget b (addr + 1)).toUInt32
  let b2 := (bget b (addr + 2)).toUInt32
  let b3 := (bget b (addr + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Little-endian 16-bit write over a `ByteArray`. -/
def bset16LE (b : ByteArray) (addr : Nat) (v : UInt16) : ByteArray :=
  bset (bset b addr v.toUInt8) (addr + 1) (v >>> 8).toUInt8

/-- Little-endian 32-bit write over a `ByteArray`. -/
def bset32LE (b : ByteArray) (addr : Nat) (v : UInt32) : ByteArray :=
  let b := bset b addr v.toUInt8
  let b := bset b (addr + 1) (v >>> 8).toUInt8
  let b := bset b (addr + 2) (v >>> 16).toUInt8
  bset b (addr + 3) (v >>> 24).toUInt8

/-- Sign-extend a byte to 32 bits (LDSB). -/
def sx8 (b : UInt8) : UInt32 :=
  if b.toNat >>> 7 == 1 then 0xFFFFFF00 ||| b.toUInt32 else b.toUInt32

/-- Sign-extend a halfword to 32 bits (LDSH). -/
def sx16 (h : UInt16) : UInt32 :=
  if h.toNat >>> 15 == 1 then 0xFFFF0000 ||| h.toUInt32 else h.toUInt32

-- ── Memory-system helpers (Phase D): mirrors, open bus, waitstates ──
-- All GBATEK numbers: memory map (mirror strides), access-time table
-- (1 + waitstates), WAITCNT fields (N code 0..3 = 4,3,2,8).

/-- Mirrored index of absolute address `a` in a region (`base`, `size`). -/
@[inline] def mirrorIdx (base size a : Nat) : Nat := (a - base) % size

/-- VRAM index: 128K window with 06018000-0601FFFF mirroring
    06010000-06017FFF (gbadoc layout). -/
@[inline] def vramIdx (a : Nat) : Nat :=
  let i := (a - 0x06000000) % 0x20000
  if i >= 0x18000 then i - 0x8000 else i

/-- Open-bus byte: last prefetched word, selected by address low bits. -/
@[inline] def openBus8 (busVal : UInt32) (a : Nat) : UInt8 :=
  ((busVal >>> (((a % 4) * 8).toUInt32)) &&& 0xFF).toUInt8

/-- N-field waitstates (WAITCNT 2-bit code, SRAM + WS0/1/2 first access). -/
def nWait (code : Nat) : Nat :=
  if code == 0 then 4 else if code == 1 then 3 else if code == 2 then 2 else 8

/-- WS0 sequential waitstates (1-bit field). -/
def sWait0 (b : Nat) : Nat := if b == 0 then 2 else 1

/-- WS1 sequential waitstates (note: 4,1 unlike WS0's 2,1). -/
def sWait1 (b : Nat) : Nat := if b == 0 then 4 else 1

/-- WS2 sequential waitstates (note: 8,1). -/
def sWait2 (b : Nat) : Nat := if b == 0 then 8 else 1
/-- Set bits of an 8-bit register mask as an ascending list (for PUSH/POP/STM/LDM). -/
def regList (mask : Nat) : List Nat :=
  (List.range 8).filter (fun i => ((mask >>> i) &&& 1) == 1)

/-- Population count of an 8-bit mask. -/
def popcount (mask : Nat) : Nat := (regList mask).length

/-- Set bits of a 16-bit register mask as an ascending list (ARM LDM/STM). -/
def regList16 (mask : Nat) : List Nat :=
  (List.range 16).filter (fun i => ((mask >>> i) &&& 1) == 1)

/-- Population count of a 16-bit mask. -/
def popcount16 (mask : Nat) : Nat := (regList16 mask).length

/-- Logical shift left with carry-out (`s = 0` = identity, carry preserved). -/
def lslRC (x : UInt32) (s : Nat) (carryIn : Bool) : UInt32 × Bool :=
  if s == 0 then (x, carryIn)
  else if s < 32 then (x <<< s.toUInt32, bitGet32 x (32 - s))
  else if s == 32 then (0, bitGet32 x 0)
  else (0, false)

/-- Logical shift right with carry-out (`s = 0` = identity). -/
def lsrRC (x : UInt32) (s : Nat) (carryIn : Bool) : UInt32 × Bool :=
  if s == 0 then (x, carryIn)
  else if s < 32 then (x >>> s.toUInt32, bitGet32 x (s - 1))
  else if s == 32 then (0, bitGet32 x 31)
  else (0, false)

/-- Arithmetic shift right with carry-out (sign-propagating). -/
def asrRC (x : UInt32) (s : Nat) (carryIn : Bool) : UInt32 × Bool :=
  if s == 0 then (x, carryIn)
  else if s < 32 then
    let r := if bitGet32 x 31
      then (x >>> s.toUInt32) ||| ((0xFFFFFFFF : UInt32) <<< ((32 - s).toUInt32))
      else x >>> s.toUInt32
    (r, bitGet32 x (s - 1))
  else ((if bitGet32 x 31 then (0xFFFFFFFF : UInt32) else 0), bitGet32 x 31)

/-- Rotate right with carry-out (`s = 0` = identity; nonzero multiples of 32 keep value, C = bit 31). -/
def rorRC (x : UInt32) (s : Nat) (carryIn : Bool) : UInt32 × Bool :=
  if s == 0 then (x, carryIn)
  else
    let k := s % 32
    if k == 0 then (x, bitGet32 x 31)
    else (rotr32 x k, bitGet32 x (k - 1))

/-- Rotate right extended (single bit through carry). -/
def rrxRC (x : UInt32) (carryIn : Bool) : UInt32 × Bool :=
  (((if carryIn then (0x80000000 : UInt32) else 0) ||| (x >>> 1)), bitGet32 x 0)

/-- ARM register-shift operand: kind 0 = LSL, 1 = LSR, 2 = ASR, 3 = ROR.
    Amount is the instruction's shift value (imm5 or Rs bottom byte);
    the zero-rules match `lslRC`/`lsrRC`/et al (LSR/ASR imm-0 callers
    must pre-map to 32, as the Thumb decoder does). -/
def armShiftReg (kind : Nat) (x : UInt32) (amount : Nat) (c0 : Bool) : UInt32 × Bool :=
  match kind with
  | 0 => lslRC x amount c0
  | 1 => lsrRC x amount c0
  | 2 => asrRC x amount c0
  | _ => rorRC x amount c0

end AGB
