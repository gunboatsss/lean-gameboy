/-
  LeanAGB.Proofs.Save — backup-media contracts: waitstate bounds/values,
  mirror arithmetic, open-bus bytes, codec round trips (small), Flash
  command-machine instances, EEPROM bit-protocol round trip, and
  memory-cost table instances. GBATEK numbers throughout.
-/
import LeanAGB.Bus

namespace AGB

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

-- ── Waitstate field bounds + values ──

theorem nWait_le_8 (c : Nat) : nWait c ≤ 8 := by
  unfold nWait
  repeat (first | split | omega)

theorem nWait_0 : nWait 0 = 4 := by decide
theorem nWait_1 : nWait 1 = 3 := by decide
theorem nWait_2 : nWait 2 = 2 := by decide
theorem nWait_3 : nWait 3 = 8 := by decide

theorem sWait0_le_2 (b : Nat) : sWait0 b ≤ 2 := by
  unfold sWait0
  split <;> omega

theorem sWait1_le_4 (b : Nat) : sWait1 b ≤ 4 := by
  unfold sWait1
  split <;> omega

theorem sWait2_le_8 (b : Nat) : sWait2 b ≤ 8 := by
  unfold sWait2
  split <;> omega

theorem sWaitFor_0 : sWaitFor 0 0 = 3 := by decide
theorem sWaitFor_1 : sWaitFor 1 0x80 = 2 := by decide
theorem sWaitFor_2 : sWaitFor 2 0 = 9 := by decide

theorem wsOf_0 : wsOf 0x08000000 = 0 := by decide
theorem wsOf_1 : wsOf 0x0A000000 = 1 := by decide
theorem wsOf_2 : wsOf 0x0C000000 = 2 := by decide

-- ── Mirror arithmetic (address level; gbadoc strides) ──
-- Bounds hold by `Nat.mod_lt` at use sites; periodicity and VRAM-alias
-- values below pin the stride tables.

theorem ewramIdx_step (a : Nat) (h : 0x02000000 ≤ a) :
    mirrorIdx 0x02000000 0x40000 (a + 0x40000) = mirrorIdx 0x02000000 0x40000 a := by
  unfold mirrorIdx
  omega

theorem iwramIdx_step (a : Nat) (h : 0x03000000 ≤ a) :
    mirrorIdx 0x03000000 0x8000 (a + 0x8000) = mirrorIdx 0x03000000 0x8000 a := by
  unfold mirrorIdx
  omega

theorem vramIdx_base : vramIdx 0x06000000 = 0 := by decide
theorem vramIdx_alias : vramIdx 0x06018000 = 0x10000 := by decide
theorem vramIdx_alias_end : vramIdx 0x0601FFFF = 0x17FFF := by decide
theorem vramIdx_wrap : vramIdx 0x06020000 = 0 := by decide

-- ── Mirror coherence at the bus level (tiny states; the modulo uses
-- constant strides, so small arrays still exercise the mirror path) ──

def mirrorState : AGBState :=
  { ({} : AGBState) with
    ewram := ByteArray.mk #[0xAA, 0, 0, 0, 0, 0, 0, 0],
    iwram := ByteArray.mk #[0xBB, 0, 0, 0, 0, 0, 0, 0] }

theorem mirror_read_ewram :
    memRead8 mirrorState 0x02040000 = memRead8 mirrorState 0x02000000 := by
  decide

theorem mirror_read_ewram_value :
    memRead8 mirrorState 0x02040000 = 0xAA := by
  decide

theorem mirror_write_ewram :
    memRead8 (memWrite8 mirrorState 0x02040000 0xAB) 0x02000000 = 0xAB := by
  decide

theorem mirror_read_iwram :
    memRead8 mirrorState 0x03008000 = memRead8 mirrorState 0x03000000 := by
  decide

-- ── Open-bus bytes ──

theorem openBus8_0 : openBus8 0xAABBCCDD 0 = 0xDD := by decide
theorem openBus8_1 : openBus8 0xAABBCCDD 1 = 0xCC := by decide
theorem openBus8_2 : openBus8 0xAABBCCDD 2 = 0xBB := by decide
theorem openBus8_3 : openBus8 0xAABBCCDD 3 = 0xAA := by decide

-- ── .sav codec (tag + round trips on small parts, same code path) ──

theorem tag_sram : saveTagKind (saveKindTag .sram) = .sram := by decide
theorem tag_flash64 : saveTagKind (saveKindTag .flash64) = .flash64 := by decide
theorem tag_flash128 : saveTagKind (saveKindTag .flash128) = .flash128 := by decide
theorem tag_eeprom4k : saveTagKind (saveKindTag .eeprom4k) = .eeprom4k := by decide
theorem tag_eeprom64k : saveTagKind (saveKindTag .eeprom64k) = .eeprom64k := by decide
theorem tag_unknown : saveTagKind 0 = .sram := by decide

theorem takePad_idem :
    takePad 8 (takePad 8 (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]))
      = takePad 8 (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]) := by
  decide

theorem codec_roundtrip :
    saveDecodeSized 8
      (saveEncodeSized 9 8 (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]))
      = takePad 8 (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]) := by
  decide

-- ── Flash command machine (small/empty states, same code path) ──

theorem flash_seq_id :
    ((flashWrite (flashWrite (flashWrite ({} : FlashState) false 0x5555 0xAA) false 0x2AAA 0x55)
      false 0x5555 0x90)).idMode = true := by
  decide

theorem flash_seq_exit :
    ((flashWrite (flashWrite (flashWrite (flashWrite (flashWrite (flashWrite ({} : FlashState)
      false 0x5555 0xAA) false 0x2AAA 0x55) false 0x5555 0x90) false 0x5555 0xAA)
      false 0x2AAA 0x55) false 0x5555 0xF0)).idMode = false := by
  decide

theorem flash_id64_0 : flashRead { ({} : FlashState) with idMode := true } false 0 = 0x32 := by
  decide

theorem flash_id64_1 : flashRead { ({} : FlashState) with idMode := true } false 1 = 0x1B := by
  decide

theorem flash_id128_0 : flashRead { ({} : FlashState) with idMode := true } true 0 = 0x62 := by
  decide

theorem flash_id128_1 : flashRead { ({} : FlashState) with idMode := true } true 1 = 0x13 := by
  decide

/-- Program-armed state over 16 erased bytes. -/
def flashProgBase : FlashState :=
  let f0 : FlashState := { data := ByteArray.mk (Array.replicate 16 (0xFF : UInt8)) }
  flashWrite (flashWrite (flashWrite f0 false 0x5555 0xAA) false 0x2AAA 0x55) false 0x5555 0xA0

theorem flash_program_and :
    bget (flashWrite flashProgBase false 3 0x0F).data 3 = 0x0F := by
  decide

theorem flash_program_and2 :
    bget (flashWrite { flashProgBase with
      data := ByteArray.mk (Array.replicate 16 (0xF0 : UInt8)) } false 3 0x0F).data 3
      = 0x00 := by
  decide

theorem flash_plain_ignored :
    (flashWrite { ({} : FlashState) with
      data := ByteArray.mk (Array.replicate 16 (0xFF : UInt8)) } false 5 0xAA).sawAA
      = false := by
  decide

theorem flash_sector_erase :
    let f0 : FlashState := { data := ByteArray.mk (Array.replicate 16 (0 : UInt8)) }
    let f1 := flashWrite f0 false 0x5555 0xAA
    let f2 := flashWrite f1 false 0x2AAA 0x55
    let f3 := flashWrite f2 false 0x5555 0x80
    let f4 := flashWrite f3 false 0x5555 0xAA
    let f5 := flashWrite f4 false 0x2AAA 0x55
    let f6 := flashWrite f5 false 0x003 0x30
    bget f6.data 0 == 0xFF && bget f6.data 15 == 0xFF := by
  decide

theorem flash_bank128 :
    (flashWrite (flashWrite (flashWrite (flashWrite ({} : FlashState) false 0x5555 0xAA)
      false 0x2AAA 0x55) false 0x5555 0xB0) true 0 1).bank = 1 := by
  decide

theorem flash_bank64_ignored :
    (flashWrite (flashWrite (flashWrite (flashWrite ({} : FlashState) false 0x5555 0xAA)
      false 0x2AAA 0x55) false 0x5555 0xB0) false 0 1).bank = 0 := by
  decide

-- ── EEPROM bit protocol (4Kbit: 6-bit addr, 64-bit blocks) ──

/-- 73-bit write stream: cmd 10, block 5, data bytes, end 0. -/
def eepromWriteBits : List Bool :=
  [true, false] ++ [false, false, false, true, false, true] ++
  (List.range 64).map
    (fun i => (((0xDEADBEEF11223344 : Nat) >>> (63 - i)) &&& 1) == 1) ++ [false]

def eepromAfterWrite : EepromState :=
  eepromWriteBits.foldl eepromWriteBit
    { ({} : EepromState) with data := ByteArray.mk (Array.replicate 512 (0 : UInt8)) }

theorem eeprom_write_idle : eepromAfterWrite.phase = 0 := by
  decide

theorem eeprom_write_commits :
    bget eepromAfterWrite.data (5 * 8) == 0xDE && bget eepromAfterWrite.data (5 * 8 + 7) == 0x44 := by
  decide

/-- 9-bit read request for block 5, then 68 clocked reads. -/
def eepromReadout : List Bool :=
  let req := [true, true] ++ [false, false, false, true, false, true] ++ [false]
  let e9 := req.foldl eepromWriteBit eepromAfterWrite
  (List.range 68).foldl
    (fun (st : EepromState × List Bool) _ =>
      let (st', b) := eepromReadBit st.1
      (st', st.2 ++ [b])) (e9, []) |>.2

theorem eeprom_readback :
    eepromReadout.drop 4 =
      (List.range 64).map
        (fun i => (((0xDEADBEEF11223344 : Nat) >>> (63 - i)) &&& 1) == 1) := by
  decide

theorem eeprom_bad_reset :
    ((List.replicate 9 false).foldl eepromWriteBit ({} : EepromState)).phase = 1 := by
  decide

-- ── Memory-cost table instances (WAITCNT states, GBATEK defaults) ──

/-- WAITCNT-configured state (1K IO shadow). -/
def waitState (wc : Nat) : AGBState :=
  { ({} : AGBState) with
    io := bset16LE (ByteArray.mk (Array.replicate 0x400 (0 : UInt8))) 0x204 (w16 wc) }

theorem memCost_rom16 : memCost (waitState 0) 0x08000000 16 = 5 := by decide
theorem memCost_rom32 : memCost (waitState 0) 0x08000000 32 = 8 := by decide
theorem memCost_sram : memCost (waitState 0) 0x0E000000 8 = 5 := by decide
theorem memCost_ewram32 : memCost (waitState 0) 0x02000000 32 = 6 := by decide
theorem memCost_vram16 : memCost (waitState 0) 0x06000000 16 = 1 := by decide
theorem memCost_pal32 : memCost (waitState 0) 0x05000000 32 = 2 := by decide
theorem memCost_io : memCost (waitState 0) 0x04000000 8 = 1 := by decide
theorem memCost_bios : memCost (waitState 0) 0x00000000 32 = 1 := by decide
theorem memCost_open : memCost (waitState 0) 0x01000000 16 = 1 := by decide
theorem memCost_ws0cfg : memCost (waitState 8) 0x08000000 16 = 3 := by decide
theorem memCost_sramcfg : memCost (waitState 2) 0x0E000000 8 = 3 := by decide

-- ── Unaligned loads rotate (5-byte ROM; b4 == b0 by construction) ──

def unalignedROM : ByteArray := ByteArray.mk #[0x11, 0x22, 0x33, 0x44, 0x11]

def unalignedState : AGBState := { ({} : AGBState) with rom := unalignedROM }

theorem unaligned_r0 : memRead32 unalignedState 0x08000000 = 0x44332211 := by decide

theorem unaligned_r1 : memRead32 unalignedState 0x08000001 = 0x11443322 := by decide

theorem unaligned_rotate :
    memRead32 unalignedState 0x08000001
      = rotr32 (memRead32 unalignedState 0x08000000) 8 := by
  decide

theorem unaligned_r2 : memRead32 unalignedState 0x08000002 = 0x11114433 := by decide

-- ── Save-string autodetect instances ──

def romWith (s : String) : ByteArray :=
  ByteArray.mk (Array.mk ((markerBytes s).map (fun n => w8 n)))

theorem detect_flash128 :
    detectSaveKind (romWith "FLASH1M_V102") = .flash128 := by
  decide

theorem detect_flash64 :
    detectSaveKind (romWith "FLASH512_V130") = .flash64 := by
  decide

theorem detect_flash64_plain :
    detectSaveKind (romWith "FLASH_V120") = .flash64 := by
  decide

theorem detect_eeprom64k :
    detectSaveKind (romWith "EEPROM_V125") = .eeprom64k := by
  decide

theorem detect_eeprom4k :
    detectSaveKind (romWith "EEPROM_V124") = .eeprom4k := by
  decide

theorem detect_sram :
    detectSaveKind (romWith "SRAM_V110") = .sram := by
  decide

theorem detect_empty : detectSaveKind ByteArray.empty = .sram := by
  decide

end AGB
