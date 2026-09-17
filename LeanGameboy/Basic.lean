/-
  LeanGameboy.Basic — small pure helpers shared by all modules.

  We deliberately avoid exotic core APIs here so the rest of the
  emulator can rely on a tiny, stable surface.
-/
namespace GB

/-- Wrap a natural into a byte. -/
def w8 (n : Nat) : UInt8 := UInt8.ofNat n

/-- Wrap a natural into a word. -/
def w16 (n : Nat) : UInt16 := UInt16.ofNat n

/-- Bit mask table so we never need variable shifts. -/
def bitMask (i : Nat) : UInt8 :=
  match i with
  | 0 => 0x01 | 1 => 0x02 | 2 => 0x04 | 3 => 0x08
  | 4 => 0x10 | 5 => 0x20 | 6 => 0x40 | _ => 0x80

/-- Test bit `i` (0 = LSB) of a byte. -/
def bitGet (x : UInt8) (i : Nat) : Bool :=
  (x &&& bitMask i) != 0

/-- Set bit `i` of a byte. -/
def bitSet (x : UInt8) (i : Nat) : UInt8 :=
  x ||| bitMask i

/-- Clear bit `i` of a byte. -/
def bitClear (x : UInt8) (i : Nat) : UInt8 :=
  x &&& ~~~(bitMask i)

/-- High byte of a 16-bit word. -/
def hiByte (v : UInt16) : UInt8 :=
  (v >>> 8).toUInt8

/-- Low byte of a 16-bit word. -/
def loByte (v : UInt16) : UInt8 :=
  v.toUInt8

/-- Join two bytes (hi, lo) into a word. -/
def join16 (hi lo : UInt8) : UInt16 :=
  (hi.toUInt16 <<< 8) ||| lo.toUInt16

/-- Add with carry-out information (for flag computation). -/
structure AddRes where
  val : UInt8
  halfCarry : Bool
  carry : Bool
deriving DecidableEq, Repr

/-- 8-bit addition, reporting half-carry (bit3→bit4) and carry. -/
def add8 (x y : UInt8) (carryIn : Bool := false) : AddRes :=
  let c := if carryIn then 1 else 0
  let total := x.toNat + y.toNat + c
  let half := (x.toNat % 16) + (y.toNat % 16) + c >= 16
  { val := w8 total, halfCarry := half, carry := total > 0xFF }

/-- Subtraction, reporting half-borrow and borrow. -/
structure SubRes where
  val : UInt8
  halfCarry : Bool
  carry : Bool
deriving DecidableEq, Repr

def sub8 (x y : UInt8) (carryIn : Bool := false) : SubRes :=
  let c := if carryIn then 1 else 0
  let total : Int := x.toNat - y.toNat - c
  let half : Bool := (x.toNat % 16 : Int) - (y.toNat % 16 : Int) - c < 0
  { val := w8 (total % 256).toNat, halfCarry := half, carry := total < 0 }

/-- Read a byte from a `ByteArray`, returning 0xFF out of bounds
    (matches Game Boy open-bus-ish behaviour for unmapped reads). -/
def bget (b : ByteArray) (addr : Nat) : UInt8 :=
  if h : addr < b.size then b[addr]'h else 0xFF

/-- Write a byte into a `ByteArray`, no-op out of bounds. -/
def bset (b : ByteArray) (addr : Nat) (v : UInt8) : ByteArray :=
  if addr < b.size then b.set! addr v else b

end GB
