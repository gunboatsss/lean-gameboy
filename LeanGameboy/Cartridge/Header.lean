/-
  LeanGameboy.Cartridge.Header — Game Boy ROM header parsing.
  See Pan Docs: "The Cartridge Header".
-/
import LeanGameboy.Basic

namespace GB

/-- Supported memory-bank controllers. -/
inductive MbcKind where
  | None | Mbc1 | Mbc2 | Mbc3 | Mbc5 | HuC1 | HuC3 | Mmm01 | Mbc6 | Mbc7
deriving DecidableEq, Repr

/-- Map the cartridge-type byte (0x0147) to an MBC kind. -/
def mbcKindOf (t : UInt8) : MbcKind :=
  match t.toNat with
  | 0x00 => .None
  | 0x01 | 0x02 | 0x03 => .Mbc1
  | 0x05 | 0x06 => .Mbc2
  | 0x08 | 0x09 => .None -- ROM+RAM(+BATT), no banking
  | 0x0B | 0x0C | 0x0D => .Mmm01
  | 0x0F | 0x10 | 0x11 | 0x12 | 0x13 => .Mbc3
  | 0x19 | 0x1A | 0x1B | 0x1C | 0x1D | 0x1E => .Mbc5
  | 0x20 => .Mbc6
  | 0x22 => .Mbc7
  | 0xFE => .HuC3
  | 0xFF => .HuC1
  | _ => .None

/-- Whether this cartridge type has battery-backed RAM. -/
def hasBattery (t : UInt8) : Bool :=
  match t.toNat with
  | 0x03 | 0x06 | 0x09 | 0x0D | 0x10 | 0x13 | 0x1B | 0x1E | 0x22 | 0xFF => true
  | _ => false

/-- ROM size code (0x0148) → number of 16 KiB banks. -/
def romBanksOf (c : UInt8) : Nat :=
  match c.toNat with
  | 0x00 => 2 | 0x01 => 4 | 0x02 => 8 | 0x03 => 16
  | 0x04 => 32 | 0x05 => 64 | 0x06 => 128 | 0x07 => 256
  | 0x08 => 512 | 0x52 => 72 | 0x53 => 80 | 0x54 => 96
  | _ => 2

/-- RAM size code (0x0149) → number of 8 KiB banks. -/
def ramBanksOf (c : UInt8) : Nat :=
  match c.toNat with
  | 0x02 => 1 | 0x03 => 4 | 0x04 => 16 | 0x05 => 8
  | _ => 0

/-- Parsed header of a loaded ROM. -/
structure CartHeader where
  title : String := ""
  cartType : UInt8 := 0
  mbc : MbcKind := .None
  battery : Bool := false
  romBanks : Nat := 2
  ramBanks : Nat := 0
  version : UInt8 := 0
  headerChecksumOk : Bool := false
deriving Repr

/-- Header checksum: `x = x - b - 1` over 0x0134..0x014C. -/
def headerChecksum (rom : ByteArray) : UInt8 :=
  (List.range (0x014D - 0x0134)).foldl
    (fun x k => x - bget rom (0x0134 + k) - 1) 0

/-- Parse the header of a ROM image. -/
def parseHeader (rom : ByteArray) : CartHeader :=
  let titleBytes := List.range 16 |>.map (fun i => bget rom (0x0134 + i))
  let title := String.ofList (titleBytes.filterMap (fun b =>
    if b == 0 then none else some (Char.ofNat b.toNat)))
  let ct := bget rom 0x0147
  let romB := romBanksOf (bget rom 0x0148)
  let ramB := ramBanksOf (bget rom 0x0149)
  { title, cartType := ct, mbc := mbcKindOf ct, battery := hasBattery ct,
    romBanks := romB, ramBanks := ramB, version := bget rom 0x014C,
    headerChecksumOk := headerChecksum rom == bget rom 0x014D }

/-- Nintendo logo bytes every DMG ROM must carry (0x0104..0x0133). -/
def nintendoLogo : Array UInt8 :=
  #[0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
    0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
    0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
    0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
    0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
    0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E]

/-- Check the logo region (boot ROM verifies this; `false` = lock up). -/
def logoOk (rom : ByteArray) : Bool :=
  nintendoLogo.size == 48 &&
    (List.range 48 |>.all fun i => bget rom (0x0104 + i) == nintendoLogo[i]!)

end GB
