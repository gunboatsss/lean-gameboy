/-
  LeanGameboy.Proofs.Mbc — cartridge header + MBC banking contracts.

  `Cartridge/Header.lean` and `Cartridge/Mbc.lean` had zero proof
  coverage (bank switching was only validated empirically via the
  Blargg composite). These pin the header codec tables, the
  parse→banking-state wiring, MBC1/MBC3 bank selection (including the
  prohibited-bank guards), and external-RAM enable/roundtrip behavior.
-/
import LeanGameboy.Cartridge.Mbc
import LeanGameboy.Proofs.Stack

namespace GB

-- `decide` over 512-byte ROM images needs headroom.
set_option maxRecDepth 100000

/-! ## Header codec tables -/

theorem kind_none : mbcKindOf 0x00 = .None := by decide

theorem kind_mbc1 : mbcKindOf 0x03 = .Mbc1 := by decide

theorem kind_mbc2 : mbcKindOf 0x06 = .Mbc2 := by decide

theorem kind_mbc3 : mbcKindOf 0x13 = .Mbc3 := by decide

theorem kind_mbc5 : mbcKindOf 0x1B = .Mbc5 := by decide

theorem kind_mbc7 : mbcKindOf 0x22 = .Mbc7 := by decide

theorem kind_huc1 : mbcKindOf 0xFF = .HuC1 := by decide

theorem kind_fallback : mbcKindOf 0x07 = .None := by decide

theorem battery_mbc1 : hasBattery 0x03 = true := by decide

theorem battery_mbc3 : hasBattery 0x13 = true := by decide

theorem battery_plain : hasBattery 0x00 = false := by decide

theorem romBanks_0 : romBanksOf 0x00 = 2 := by decide

theorem romBanks_1 : romBanksOf 0x01 = 4 := by decide

theorem romBanks_7 : romBanksOf 0x07 = 256 := by decide

theorem romBanks_8 : romBanksOf 0x08 = 512 := by decide

theorem romBanks_fallback : romBanksOf 0xFF = 2 := by decide

theorem ramBanks_0 : ramBanksOf 0x00 = 0 := by decide

theorem ramBanks_2 : ramBanksOf 0x02 = 1 := by decide

theorem ramBanks_3 : ramBanksOf 0x03 = 4 := by decide

theorem ramBanks_5 : ramBanksOf 0x05 = 8 := by decide

theorem cgb_compat : cgbFlagOf 0x80 = .Compatible := by decide

theorem cgb_excl : cgbFlagOf 0xC0 = .Exclusive := by decide

theorem cgb_dmg : cgbFlagOf 0x00 = .Dmg := by decide

/-! ## Header parsing -/

/-- Minimal MBC1 ROM: type 0x03, 4 ROM banks, 1 RAM bank. -/
def mbc1ROM : ByteArray :=
  let blank := ByteArray.mk (Array.replicate 0x200 (0 : UInt8))
  bset (bset (bset blank 0x0147 0x03) 0x0148 0x01) 0x0149 0x02

theorem parse_mbc1 : (parseHeader mbc1ROM).mbc = .Mbc1 := by decide

theorem parse_mbc1_romBanks : (parseHeader mbc1ROM).romBanks = 4 := by decide

theorem parse_mbc1_ramBanks : (parseHeader mbc1ROM).ramBanks = 1 := by decide

theorem parse_mbc1_battery : (parseHeader mbc1ROM).battery = true := by decide

/-- Parsing feeds banking state directly. -/
theorem ofHeader_kind (h : CartHeader) :
    (MbcState.ofHeader h).kind = h.mbc := rfl

theorem ofHeader_romBanks (h : CartHeader) :
    (MbcState.ofHeader h).romBanks = h.romBanks := rfl

theorem ofHeader_ramBanks (h : CartHeader) :
    (MbcState.ofHeader h).ramBanks = h.ramBanks := rfl

theorem ofHeader_parse_romBanks :
    (MbcState.ofHeader (parseHeader mbc1ROM)).romBanks = 4 := by decide

/-! ## Boot logo -/

theorem logo_empty : logoOk ByteArray.empty = false := by decide

/-- ROM carrying the exact Nintendo logo passes. -/
def logoROM : ByteArray :=
  let blank := ByteArray.mk (Array.replicate 0x200 (0 : UInt8))
  (List.range 48).foldl
    (fun b i => bset b (0x0104 + i) nintendoLogo[i]!) blank

theorem logo_ok : logoOk logoROM = true := by decide

/-! ## MBC1 bank selection -/

/-- The switchable ROM bank always folds into range. -/
theorem mbc1RomBank_bounds (s : MbcState) (h : 0 < s.romBanks) :
    mbc1RomBank s < s.romBanks := by
  unfold mbc1RomBank
  exact Nat.mod_lt _ h

/-- The bank-0 area selector always folds into range. -/
theorem mbc1Bank0_bounds (s : MbcState) (h : 0 < s.romBanks) :
    mbc1Bank0 s < s.romBanks := by
  unfold mbc1Bank0
  split
  · exact Nat.mod_lt _ h
  · omega

/-- Bank 0 of the low 5 bits is prohibited: maps to 1. -/
theorem mbc1RomBank_zero_lo :
    mbc1RomBank { kind := .Mbc1, romBanks := 128, romBank := 0 } = 1 := by
  decide

theorem mbc1RomBank_passthrough :
    mbc1RomBank { kind := .Mbc1, romBanks := 128, romBank := 3 } = 3 := by
  decide

/-! ## Cartridge reads -/

/-- NoMBC reads are identity. -/
theorem cartRead_none (rom : ByteArray) (s : MbcState) (addr : Nat)
    (h : s.kind = .None) :
    cartRead rom s addr = bget rom addr := by
  simp [cartRead, h]

/-- Unmodelled mappers read flat. -/
theorem cartRead_mbc2_flat (rom : ByteArray) (s : MbcState) (addr : Nat)
    (h : s.kind = .Mbc2) :
    cartRead rom s addr = bget rom addr := by
  simp [cartRead, h]

/-- MBC1 fixed area reads through the bank-0 selector. -/
theorem cartRead_mbc1_fixed (rom : ByteArray) (s : MbcState) (addr : Nat)
    (hkind : s.kind = .Mbc1) (haddr : addr < 0x4000) :
    cartRead rom s addr =
      bget rom ((mbc1Bank0 s % s.romBanks) * 0x4000 + addr % 0x4000) := by
  simp [cartRead, hkind, haddr]

/-- MBC3 maps a zero ROM bank to 1. -/
theorem cartRead_mbc3_zero_bank (rom : ByteArray) (addr : Nat)
    (haddr : 0x4000 ≤ addr) :
    cartRead rom { kind := .Mbc3, romBanks := 128, romBank := 0 } addr =
      bget rom (1 * 0x4000 + addr % 0x4000) := by
  have e1 : ¬ addr < 0x4000 := by omega
  simp [cartRead, e1]

/-! ## RAM-bank selection -/

theorem ramSel_mbc1_romMode : ramSel { kind := .Mbc1, mode := false } = 0 := by
  decide

theorem ramSel_none : ramSel { kind := .None } = 0 := by decide

/-! ## Banking-register writes -/

theorem cartWrite_ramEnable :
    (cartWrite {} 0x0000 0x0A).ramEnabled = true := by decide

theorem cartWrite_ramDisable :
    (cartWrite { ramEnabled := true } 0x0000 0x00).ramEnabled = false := by
  decide

theorem cartWrite_mbc1_lo :
    (cartWrite { kind := .Mbc1, romBank := 0 } 0x2000 0x03).romBank = 3 := by
  decide

theorem cartWrite_mbc1_mode :
    (cartWrite { kind := .Mbc1 } 0x6000 0x01).mode = true := by decide

theorem cartWrite_mbc1_ramBank :
    (cartWrite { kind := .Mbc1, mode := true } 0x4000 0x02).ramBank = 2 := by
  decide

theorem cartWrite_mbc5_hi :
    (cartWrite { kind := .Mbc5, romBank := 1 } 0x3000 0x01).romBank = 257 := by
  decide

/-! ## External RAM -/

/-- Disabled RAM reads open (`0xFF`). -/
theorem extRamRead_disabled (r : ExtRam) (s : MbcState) (addr : Nat)
    (h : s.ramEnabled = false) :
    extRamRead r s addr = 0xFF := by
  simp [extRamRead, h]

/-- Disabled RAM writes are dropped. -/
theorem extRamWrite_disabled (r : ExtRam) (s : MbcState) (addr : Nat)
    (v : UInt8) (h : s.ramEnabled = false) :
    extRamWrite r s addr v = r := by
  simp [extRamWrite, h]

/-- Enabled RAM reads back what was written. -/
theorem extRam_rw (r : ExtRam) (s : MbcState) (addr : Nat) (v : UInt8)
    (hen : s.ramEnabled = true)
    (hb : ramSel s < r.banks.size)
    (hoff : addr - 0xA000 < (r.banks[ramSel s]'hb).size) :
    extRamRead (extRamWrite r s addr v) s addr = v := by
  have hsome : r.banks[ramSel s]? = some (r.banks[ramSel s]'hb) :=
    Array.getElem?_eq_getElem hb
  have hW : extRamWrite r s addr v =
      { banks :=
        r.banks.setIfInBounds (ramSel s) (bset (r.banks[ramSel s]'hb) (addr - 0xA000) v) } := by
    simp [extRamWrite, hen, hsome]
  rw [hW]
  have h2 :=
    Array.getElem_setIfInBounds (xs := r.banks) (i := ramSel s)
      (a := bset (r.banks[ramSel s]'hb) (addr - 0xA000) v) (j := ramSel s) hb
  simp only [ite_true] at h2
  have hsize :=
    Array.size_setIfInBounds (xs := r.banks) (i := ramSel s)
      (a := bset (r.banks[ramSel s]'hb) (addr - 0xA000) v)
  have hdi :
      ramSel s <
        (r.banks.setIfInBounds (ramSel s)
          (bset (r.banks[ramSel s]'hb) (addr - 0xA000) v)).size := by
    rw [hsize]; exact hb
  have hget :
      ((r.banks.setIfInBounds (ramSel s)
        (bset (r.banks[ramSel s]'hb) (addr - 0xA000) v))[ramSel s]?) =
        some (bset (r.banks[ramSel s]'hb) (addr - 0xA000) v) := by
    rw [Array.getElem?_eq_getElem hdi, h2]
  have hR :
      extRamRead
        ({ banks :=
          r.banks.setIfInBounds (ramSel s) (bset (r.banks[ramSel s]'hb) (addr - 0xA000) v) } : ExtRam)
        s addr =
        bget (bset (r.banks[ramSel s]'hb) (addr - 0xA000) v) (addr - 0xA000) := by
    simp [extRamRead, hen, hget]
  rw [hR]
  exact bget_bset_same _ _ _ hoff

end GB
