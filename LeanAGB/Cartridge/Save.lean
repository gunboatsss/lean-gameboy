/-
  LeanAGB.Cartridge.Save — backup media: SRAM, Flash64/128, EEPROM 4K/64K.
  Numbers/pins from GBATEK (cartridges) + Beliveau (flash sequences) +
  DenSinH (EEPROM bit protocol). All state pure; timings live in Bus.
-/
import LeanAGB.Basic

namespace AGB

/-- Backup-media kind (selected by `--save`, `auto` by default;
    `.sav` tag overrides). -/
inductive SaveKind where
  | sram : SaveKind
  | flash64 : SaveKind
  | flash128 : SaveKind
  | eeprom4k : SaveKind
  | eeprom64k : SaveKind
deriving DecidableEq, Repr, Inhabited

-- ── Save-type autodetect (ROM ID strings, cf. VBA database) ──
-- Games embed one of these markers; 64K EEPROMs are exactly the
-- V125/V126 IDs, everything else EEPROM_* is 4K. Unknown → SRAM.

/-- Match `marker` bytes at file offset `off` (bounds-safe). -/
def matchesAt : ByteArray → List Nat → Nat → Bool
  | _, [], _ => true
  | rom, m :: ms, off =>
    off < rom.size && (bget rom off).toNat == m && matchesAt rom ms (off + 1)

/-- Sliding marker search (`fuel` bounds the scan for termination). -/
def hasMarkerAux (rom : ByteArray) (marker : List Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, off =>
    if matchesAt rom marker off then true
    else hasMarkerAux rom marker fuel (off + 1)

def hasMarker (rom : ByteArray) (marker : List Nat) : Bool :=
  if marker.isEmpty then false
  else hasMarkerAux rom marker (rom.size + 1) 0

def markerBytes (s : String) : List Nat := s.toList.map Char.toNat

def detectSaveKind (rom : ByteArray) : SaveKind :=
  if hasMarker rom (markerBytes "FLASH1M_V") then .flash128
  else if hasMarker rom (markerBytes "FLASH512_V")
      || hasMarker rom (markerBytes "FLASH_V") then .flash64
  else if hasMarker rom (markerBytes "EEPROM_V125")
      || hasMarker rom (markerBytes "EEPROM_V126") then .eeprom64k
  else if hasMarker rom (markerBytes "EEPROM_V") then .eeprom4k
  else if hasMarker rom (markerBytes "SRAM_V") then .sram
  else .sram

/-- Flash command state (Beliveau sequences, all games use one type/size). -/
structure FlashState where
  data : ByteArray := ByteArray.empty
  bank : Nat := 0
  sawAA : Bool := false
  saw55 : Bool := false
  eraseSetup : Bool := false
  progNext : Bool := false
  bankNext : Bool := false
  idMode : Bool := false

/-- EEPROM serial state (DenSinH bit protocol; one bus access = one bit). -/
structure EepromState where
  data : ByteArray := ByteArray.empty
  addrBits : Nat := 6
  blocks : Nat := 64
  phase : Nat := 0  -- 0 idle, 1 header-in, 2 data-in, 3 data-out
  isRead : Bool := false
  recv : Nat := 0
  nbits : Nat := 0
  addr : Nat := 0
  dataAcc : Nat := 0
  outPos : Nat := 0

structure SaveState where
  kind : SaveKind := .sram
  sram : ByteArray := ByteArray.empty
  flash : FlashState := {}
  eeprom : EepromState := {}

/-- Fresh (erased) media: flash/EEPROM power up 0xFF, SRAM zeroed. -/
def SaveState.fresh (kind : SaveKind) : SaveState :=
  let ff (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n (0xFF : UInt8))
  let zz (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n (0 : UInt8))
  match kind with
  | .sram => { kind := .sram, sram := zz 0x10000 }
  | .flash64 => { kind := .flash64, flash := { data := ff 0x10000 } }
  | .flash128 => { kind := .flash128, flash := { data := ff 0x20000 } }
  | .eeprom4k => { kind := .eeprom4k, eeprom := { data := ff 512, addrBits := 6, blocks := 64 } }
  | .eeprom64k => { kind := .eeprom64k, eeprom := { data := ff 8192, addrBits := 14, blocks := 1024 } }

/-- Chip IDs: Panasonic 64K (0x32/0x1B), Sanyo 128K (0x62/0x13). -/
def flashId (is128 : Bool) (off : Nat) : UInt8 :=
  if off == 0 then (if is128 then 0x62 else 0x32)
  else if off == 1 then (if is128 then 0x13 else 0x1B)
  else 0xFF

/-- Bank base for 64K-window reads/writes (128K only). -/
def flashBankBase (is128 : Bool) (bank : Nat) : Nat :=
  if is128 then (bank % 2) * 0x10000 else 0

def flashRead (fl : FlashState) (is128 : Bool) (off : Nat) : UInt8 :=
  if fl.idMode && off < 2 then flashId is128 off
  else bget fl.data (flashBankBase is128 fl.bank + off)

/-- Erase `n` bytes at `pos` (clamped by `bset` bounds) to 0xFF. -/
def flashEraseRange : ByteArray → Nat → Nat → ByteArray
  | b, _, 0 => b
  | b, pos, k + 1 => flashEraseRange (bset b pos 0xFF) (pos + 1) k

/-- One byte-write into the 0x0E window (`off` = offset, already mod 64K).
    Plain writes to array space are IGNORED (flash needs sequences);
    programming ANDs bits (1→0 only); erases fill 0xFF. -/
def flashWrite (fl : FlashState) (is128 : Bool) (off : Nat) (v : UInt8) : FlashState :=
  let base := flashBankBase is128 fl.bank
  if fl.progNext then
    let i := base + off
    { fl with data := bset fl.data i ((bget fl.data i) &&& v), progNext := false, sawAA := false, saw55 := false, eraseSetup := false }
  else if fl.bankNext then
    { fl with bank := if is128 && off == 0 then v.toNat % 2 else fl.bank, bankNext := false, sawAA := false, saw55 := false }
  else if fl.sawAA && fl.saw55 then
    if off == 0x5555 then
      if v == 0x90 then
        { fl with idMode := true, sawAA := false, saw55 := false, eraseSetup := false }
      else if v == 0xF0 then
        { fl with idMode := false, eraseSetup := false, progNext := false, bankNext := false, sawAA := false, saw55 := false }
      else if v == 0x80 then
        { fl with eraseSetup := true, sawAA := false, saw55 := false }
      else if v == 0xA0 then
        { fl with progNext := true, sawAA := false, saw55 := false }
      else if v == 0xB0 then
        { fl with bankNext := true, sawAA := false, saw55 := false }
      else if v == 0x10 && fl.eraseSetup then
        { fl with data := flashEraseRange fl.data 0 fl.data.size, eraseSetup := false, sawAA := false, saw55 := false }
      else
        { fl with eraseSetup := false, sawAA := false, saw55 := false }
    else if v == 0x30 && fl.eraseSetup then
      -- sector erase: 4K at the addressed sector within the bank window
      let sec := base + ((off % 0x10000) / 0x1000) * 0x1000
      { fl with data := flashEraseRange fl.data sec 0x1000, eraseSetup := false, sawAA := false, saw55 := false }
    else
      { fl with eraseSetup := false, sawAA := false, saw55 := false }
  else if off == 0x5555 && v == 0xAA then { fl with sawAA := true }
  else if off == 0x2AAA && v == 0x55 && fl.sawAA then { fl with saw55 := true }
  else if v == 0xF0 then
    -- lone 0xF0 terminates a program-wait; otherwise ignored (ready stays)
    { fl with progNext := false, eraseSetup := false, sawAA := false, saw55 := false }
  else { fl with sawAA := false, saw55 := false }

/-- One EEPROM bus write (single bit = bit 0). -/
def eepromWriteBit (e : EepromState) (bit : Bool) : EepromState :=
  if e.phase == 0 then
    { e with phase := 1, recv := (if bit then 1 else 0), nbits := 1 }
  else if e.phase == 1 then
    let recv := e.recv * 2 + (if bit then 1 else 0)
    let nbits := e.nbits + 1
    if nbits == 2 + e.addrBits then
      let cmd := recv >>> e.addrBits
      let addr := (recv % (2 ^ e.addrBits)) % e.blocks
      if cmd == 0b11 then
        -- read: one trailing bit still to come
        { e with recv := recv, nbits := nbits, isRead := true, addr := addr }
      else if cmd == 0b10 then
        -- write: next bit is already data bit 0
        { e with phase := 2, dataAcc := 0, nbits := 0, recv := 0, isRead := false, addr := addr }
      else { e with phase := 0, recv := 0, nbits := 0 }
    else if nbits == 2 + e.addrBits + 1 then
      -- trailing bit (must be 0 on HW; lenient here)
      if e.isRead then { e with phase := 3, outPos := 0, nbits := 0, recv := 0 }
      else { e with phase := 2, dataAcc := 0, nbits := 0, recv := 0 }
    else { e with recv := recv, nbits := nbits }
  else if e.phase == 2 then
    if e.nbits + 1 == 65 then
      -- trailing bit: commit the collected 64-bit block MSB-first
      -- (trailing value ignored, lenient)
      let bytes := (List.range 8).foldl
        (fun b j => bset b (e.addr * 8 + j)
          (w8 ((e.dataAcc >>> ((7 - j) * 8)) &&& 0xFF))) e.data
      { e with data := bytes, phase := 0, nbits := 0, recv := 0, dataAcc := 0 }
    else { e with dataAcc := e.dataAcc * 2 + (if bit then 1 else 0), nbits := e.nbits + 1 }
  else e  -- data-out: writes ignored

/-- One EEPROM bus read: bit 0 carries data (rest 0); idle reads 1. -/
def eepromReadBit (e : EepromState) : EepromState × Bool :=
  if e.phase == 3 then
    if e.outPos < 4 then ({ e with outPos := e.outPos + 1 }, false)
    else if e.outPos < 68 then
      let i := e.outPos - 4
      let bit := ((bget e.data (e.addr * 8 + i / 8)).toNat >>> (7 - (i % 8))) &&& 1 == 1
      ({ e with outPos := e.outPos + 1 }, bit)
    else ({ e with phase := 0, outPos := 0, nbits := 0 }, true)
  else (e, true)

-- ── .sav codec: [tag byte] ++ payload (sizes per kind) ──

def saveKindTag : SaveKind → UInt8
  | .sram => 1 | .flash64 => 2 | .flash128 => 3 | .eeprom4k => 4 | .eeprom64k => 5

def saveTagKind : UInt8 → SaveKind
  | 1 => .sram | 2 => .flash64 | 3 => .flash128 | 4 => .eeprom4k | 5 => .eeprom64k
  | _ => .sram

/-- Payload size per kind (unknown/empty tags decode as SRAM). -/
def saveKindSize : SaveKind → Nat
  | .sram => 0x10000 | .flash64 => 0x10000 | .flash128 => 0x20000
  | .eeprom4k => 512 | .eeprom64k => 8192

def saveParts (sv : SaveState) : ByteArray :=
  match sv.kind with
  | .sram => sv.sram
  | .flash64 => sv.flash.data
  | .flash128 => sv.flash.data
  | .eeprom4k => sv.eeprom.data
  | .eeprom64k => sv.eeprom.data

/-- Truncate-or-zero-pad to exactly `n` bytes. -/
def takePad (n : Nat) (b : ByteArray) : ByteArray :=
  let t := b.extract 0 (min n b.size)
  t ++ ByteArray.mk (Array.replicate (n - t.size) (0 : UInt8))

/-- Size-explicit core (table wrapper below); same code path, testable small. -/
def saveEncodeSized (tag : UInt8) (size : Nat) (part : ByteArray) : ByteArray :=
  ByteArray.mk #[tag] ++ takePad size part

def saveDecodeSized (size : Nat) (bytes : ByteArray) : ByteArray :=
  takePad size (if bytes.size == 0 then ByteArray.empty else bytes.extract 1 bytes.size)

def saveEncode (sv : SaveState) : ByteArray :=
  saveEncodeSized (saveKindTag sv.kind) (saveKindSize sv.kind) (saveParts sv)

def saveDecode (bytes : ByteArray) : SaveState :=
  let kind := if bytes.size == 0 then .sram else saveTagKind (bget bytes 0)
  let part := saveDecodeSized (saveKindSize kind) bytes
  let base := SaveState.fresh kind
  match kind with
  | .sram => { base with sram := part }
  | .flash64 => { base with flash := { base.flash with data := part } }
  | .flash128 => { base with flash := { base.flash with data := part } }
  | .eeprom4k => { base with eeprom := { base.eeprom with data := part } }
  | .eeprom64k => { base with eeprom := { base.eeprom with data := part } }

end AGB
