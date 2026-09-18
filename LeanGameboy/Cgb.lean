/-
  LeanGameboy.Cgb — Game Boy Color hardware extensions.

  Pure helpers for the CGB feature set (Pan Docs "CGB Registers"):
  WRAM banking (SVBK), VRAM banking (VBK), 15-bit palette RAM with
  auto-increment index registers (BGPI/BGPD, OBPI/OBPD), speed control
  (KEY1), and HDMA transfer state. The bus mappings and transfer
  execution live in `Bus` (they need full `GBState` access).
-/
import LeanGameboy.Basic

namespace GB

/-- WRAM bank size (4 KiB) and total CGB WRAM (8 banks = 32 KiB). -/
def wramBankSize : Nat := 0x1000
def wramCgbSize : Nat := 0x8000

/-- VRAM bank size (8 KiB) and total CGB VRAM (2 banks = 16 KiB). -/
def vramBankSize : Nat := 0x2000
def vramCgbSize : Nat := 0x4000

/-- Selected WRAM bank for 0xD000..0xDFFF (SVBK low 3 bits, 0 maps to 1). -/
def wramBank (svbk : UInt8) : Nat :=
  let b := svbk.toNat % 8
  if b == 0 then 1 else b

/-- Selected VRAM bank for 0x8000..0x9FFF (VBK bit 0). -/
def vramBank (vbk : UInt8) : Nat :=
  vbk.toNat % 2

/-- Physical WRAM offset for CPU address `addr` in 0xC000..0xDFFF. -/
def wramPhys (svbk : UInt8) (addr : Nat) : Nat :=
  if addr < 0xD000 then addr - 0xC000
  else wramBank svbk * wramBankSize + (addr - 0xD000)

/-- Physical VRAM offset for CPU address `addr` in 0x8000..0x9FFF. -/
def vramPhys (vbk : UInt8) (addr : Nat) : Nat :=
  vramBank vbk * vramBankSize + (addr - 0x8000)

/-- Read banked WRAM (CGB sizes; DMG callers pass svbk = 1 with a
    0x2000-byte array — `bget` returns 0xFF out of bounds, matching
    open-bus-ish behaviour). -/
def wramRead (wram : ByteArray) (svbk : UInt8) (addr : Nat) : UInt8 :=
  bget wram (wramPhys svbk addr)

/-- Write banked WRAM (no-op out of bounds). -/
def wramWrite (wram : ByteArray) (svbk : UInt8) (addr : Nat) (v : UInt8) : ByteArray :=
  bset wram (wramPhys svbk addr) v

/-- Read banked VRAM. -/
def vramRead (vram : ByteArray) (vbk : UInt8) (addr : Nat) : UInt8 :=
  bget vram (vramPhys vbk addr)

/-- Write banked VRAM. -/
def vramWrite (vram : ByteArray) (vbk : UInt8) (addr : Nat) (v : UInt8) : ByteArray :=
  bset vram (vramPhys vbk addr) v

/-! ## Palette RAM -/

/-- CGB palette RAM: 8 palettes × 4 colors of BGR555, flat 32 entries.
    Boot ROM initializes all to white. -/
def palFresh : Array UInt16 :=
  Array.mk (List.replicate 32 0x7FFF)

/-- Get a palette entry (0..31). -/
def palGet (pal : Array UInt16) (i : Nat) : UInt16 :=
  if h : i < pal.size then pal[i]'h else 0x7FFF

/-- Set a palette entry. -/
def palSet (pal : Array UInt16) (i : Nat) (c : UInt16) : Array UInt16 :=
  if i < pal.size then pal.set! i c else pal

/-- Read one byte of a palette entry (even = low, odd = high). -/
def palReadByte (pal : Array UInt16) (idx : Nat) : UInt8 :=
  let c := palGet pal (idx / 2)
  if idx % 2 == 0 then c.toUInt8 else (c >>> 8).toUInt8

/-- Write one byte of a palette entry. -/
def palWriteByte (pal : Array UInt16) (idx : Nat) (v : UInt8) : Array UInt16 :=
  let i := idx / 2
  let c := palGet pal i
  let c' :=
    if idx % 2 == 0 then (c &&& (0xFF00 : UInt16)) ||| v.toUInt16
    else (c &&& (0x00FF : UInt16)) ||| (v.toUInt16 <<< 8)
  palSet pal i c'

/-- Advance an auto-increment palette index (wraps at 63 → 0). -/
def palAutoInc (reg : UInt8) : UInt8 :=
  if bitGet reg 7 then
    let next := (reg.toNat + 1) % 64
    w8 (0x80 + next)
  else reg

/-- Convert BGR555 to ARGB888 (5→8 bit expansion replicates top bits). -/
def cgbColor (c : UInt16) : UInt32 :=
  let n := c.toNat
  let r := n % 32
  let g := (n / 32) % 32
  let b := (n / 1024) % 32
  let expand (v : Nat) : UInt32 :=
    UInt32.ofNat (v <<< 3) ||| UInt32.ofNat (v >>> 2)
  (0xFF000000 : UInt32) ||| (expand r <<< 16) ||| (expand g <<< 8) ||| expand b

/-! ## HDMA -/

/-- HDMA transfer state (registers FF51..FF55). -/
structure HdmaState where
  src : Nat := 0  -- 16-bit source address (low nibble forced to 0)
  dst : Nat := 0  -- VRAM destination offset 0..0x1FF0 (low nibble forced to 0)
  remaining : Nat := 0 -- bytes left to transfer
  active : Bool := false -- HBlank DMA in progress
deriving DecidableEq, Repr

namespace HdmaState

/-- Length byte → total bytes ((len + 1) * 16). -/
def totalLen (v : UInt8) : Nat :=
  (v.toNat % 128 + 1) * 16

/-- HDMA5 read value: bit 7 = 0 while active, low 7 = remaining blocks - 1. -/
def statusReg (h : HdmaState) : UInt8 :=
  let blocks := (h.remaining + 15) / 16
  (if h.active then 0x00 else 0x80) ||| w8 ((if blocks == 0 then 0 else blocks - 1) % 128)

end HdmaState

end GB
