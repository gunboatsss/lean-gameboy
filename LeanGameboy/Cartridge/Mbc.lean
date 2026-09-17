/-
  LeanGameboy.Cartridge.Mbc — NoMBC / MBC1 / MBC3 / MBC5 banking.

  Pure functions: `cartRead` maps a CPU address to a ROM byte,
  `cartWrite` updates banking state / external RAM.
  MBC2/MMM01/HuC/MBC6/7 are not banked here (treated as NoMBC for
  reads; only MBC1+3+5 are fully modelled, per v1 scope).
-/
import LeanGameboy.Basic
import LeanGameboy.Cartridge.Header

namespace GB

/-- Mutable banking state of the cartridge. -/
structure MbcState where
  kind : MbcKind := .None
  romBanks : Nat := 2
  ramBanks : Nat := 0
  -- banking registers
  romBank : Nat := 1
  ramBank : Nat := 0
  ramEnabled : Bool := false
  mode : Bool := false       -- MBC1: false = ROM mode, true = RAM mode
  rtcLatch : Bool := false   -- MBC3: latch state (RTC values stubbed)
deriving DecidableEq, Repr

/-- Fresh MBC state for a parsed header. -/
def MbcState.ofHeader (h : CartHeader) : MbcState :=
  { kind := h.mbc, romBanks := h.romBanks, ramBanks := h.ramBanks }

/-- Effective switchable ROM bank for MBC1. Bank 0 of the low 5 bits
    is prohibited (maps to 1). -/
def mbc1RomBank (s : MbcState) : Nat :=
  let lo5 := s.romBank % 32
  let lo := if lo5 == 0 then 1 else lo5
  let hi := if s.mode then 0 else (s.ramBank % 4) * 32
  (hi + lo) % s.romBanks

/-- ROM bank 0 area under MBC1 RAM-banking mode. -/
def mbc1Bank0 (s : MbcState) : Nat :=
  if s.mode then ((s.ramBank % 4) * 32) % s.romBanks else 0

/-- Read a byte from cartridge ROM space (0x0000..0x7FFF). -/
def cartRead (rom : ByteArray) (s : MbcState) (addr : Nat) : UInt8 :=
  let off : Nat → Nat := fun bank => (bank % s.romBanks) * 0x4000 + (addr % 0x4000)
  match s.kind with
  | .None => bget rom addr
  | .Mbc1 =>
    if addr < 0x4000 then bget rom (off (mbc1Bank0 s))
    else bget rom (off (mbc1RomBank s))
  | .Mbc3 =>
    if addr < 0x4000 then bget rom addr
    else
      let b := if s.romBank % 128 == 0 then 1 else s.romBank % 128
      bget rom (off b)
  | .Mbc5 =>
    if addr < 0x4000 then bget rom addr
    else bget rom (off s.romBank)
  | _ => bget rom addr -- unmodelled mappers: flat read

/-- External RAM: banks of 8 KiB. -/
structure ExtRam where
  banks : Array ByteArray := #[]

/-- Allocate zeroed external RAM. -/
def ExtRam.fresh (n : Nat) : ExtRam :=
  { banks := Array.mk (List.replicate n (ByteArray.mk (Array.mk (List.replicate 0x2000 0)))) }

/-- Selected RAM bank index (MBC1 RAM mode uses ramBank; else bank 0). -/
def ramSel (s : MbcState) : Nat :=
  match s.kind with
  | .Mbc1 => if s.mode then s.ramBank % 4 else 0
  | .Mbc3 | .Mbc5 => s.ramBank
  | _ => 0

/-- Read external RAM (0xA000..0xBFFF). -/
def extRamRead (r : ExtRam) (s : MbcState) (addr : Nat) : UInt8 :=
  if !s.ramEnabled then 0xFF
  else
    let b := ramSel s
    match r.banks[b]? with
    | none => 0xFF
    | some bank => bget bank (addr - 0xA000)

/-- Write external RAM. -/
def extRamWrite (r : ExtRam) (s : MbcState) (addr : Nat) (v : UInt8) : ExtRam :=
  if !s.ramEnabled then r
  else
    let b := ramSel s
    match r.banks[b]? with
    | none => r
    | some bank =>
      { banks := r.banks.set! b (bset bank (addr - 0xA000) v) }

/-- Handle a write to ROM space (banking registers). -/
def cartWrite (s : MbcState) (addr : Nat) (v : UInt8) : MbcState :=
  let n := v.toNat
  if addr < 0x2000 then
    { s with ramEnabled := (n % 16 == 0x0A) }
  else match s.kind with
  | .Mbc1 =>
    if addr < 0x4000 then
      { s with romBank := (s.romBank &&& 0x60) ||| (n % 32) }
    else if addr < 0x6000 then
      if s.mode then { s with ramBank := n % 4 }
      else { s with romBank := ((n % 4) * 32) ||| (s.romBank % 32) }
    else { s with mode := (n % 2 == 1) }
  | .Mbc3 =>
    if addr < 0x4000 then
      { s with romBank := n % 128 }
    else if addr < 0x6000 then
      { s with ramBank := n }
    else
      -- latch sequence 0x00 → 0x01; RTC registers stubbed
      { s with rtcLatch := (n == 0x01) }
  | .Mbc5 =>
    if addr < 0x3000 then
      { s with romBank := ((s.romBank / 256) * 256) + n }
    else if addr < 0x4000 then
      { s with romBank := ((n % 2) * 256) + (s.romBank % 256) }
    else if addr < 0x6000 then
      { s with ramBank := n % 16 }
    else s
  | _ => s

end GB
