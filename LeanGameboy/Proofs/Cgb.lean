/-
  LeanGameboy.Proofs.Cgb — Game Boy Color banking/palette/HDMA contracts.

  `Cgb.lean` is pure helpers with zero prior coverage (`Proofs/Bus`
  only pins HDMA *cycle* preservation). These pin the value semantics
  `gb-test` checks empirically: WRAM/VRAM bank selection + isolation,
  palette RAM read-after-write + auto-increment, BGR555→ARGB pins, and
  HDMA length/status registers.
-/
import LeanGameboy.Cgb
import LeanGameboy.Proofs.Stack

namespace GB

/-! ## WRAM banking (SVBK) -/

/-- Selected WRAM bank is always 1..7 (0 maps to 1). -/
theorem wramBank_bounds (svbk : UInt8) :
    1 ≤ wramBank svbk ∧ wramBank svbk ≤ 7 := by
  have hmod : svbk.toNat % 8 < 8 := by omega
  by_cases h : (svbk.toNat % 8 == 0) = true
  · unfold wramBank
    dsimp only
    rw [ite_eq_left h]
    omega
  · have hne : svbk.toNat % 8 ≠ 0 := fun heq => h (by rw [heq]; decide)
    unfold wramBank
    dsimp only
    rw [ite_eq_right h]
    omega

theorem wramBank_zero : wramBank 0 = 1 := by decide

theorem wramBank_one : wramBank 1 = 1 := by decide

theorem wramBank_seven : wramBank 7 = 7 := by decide

theorem wramBank_wrap : wramBank 8 = 1 := by decide

/-! ## VRAM banking (VBK) -/

/-- Selected VRAM bank is 0 or 1. -/
theorem vramBank_lt2 (vbk : UInt8) : vramBank vbk < 2 := by
  unfold vramBank
  omega

theorem vramBank_0 : vramBank 0 = 0 := by decide

theorem vramBank_1 : vramBank 1 = 1 := by decide

theorem vramBank_2 : vramBank 2 = 0 := by decide

/-! ## Physical offsets -/

/-- Fixed WRAM region ignores the bank register. -/
theorem wramPhys_fixed (svbk svbk' : UInt8) (addr : Nat)
    (h : addr < 0xD000) :
    wramPhys svbk addr = wramPhys svbk' addr := by
  simp [wramPhys, h]

/-- Banked WRAM offsets stay inside the 32 KiB CGB window. -/
theorem wramPhys_lt_cgb (svbk : UInt8) (addr : Nat)
    (h : addr < 0xE000) :
    wramPhys svbk addr < wramCgbSize := by
  have hb := wramBank_bounds svbk
  unfold wramPhys wramCgbSize wramBankSize
  split
  · omega
  · omega

/-- VRAM offsets stay inside the 16 KiB CGB window. -/
theorem vramPhys_lt_cgb (vbk : UInt8) (addr : Nat)
    (h1 : 0x8000 ≤ addr) (h2 : addr < 0xA000) :
    vramPhys vbk addr < vramCgbSize := by
  have hb := vramBank_lt2 vbk
  unfold vramPhys vramCgbSize vramBankSize
  omega

/-! ## Banked read-after-write + isolation -/

/-- Reading back a banked WRAM write. -/
theorem wram_rw (wram : ByteArray) (svbk : UInt8) (addr : Nat) (v : UInt8)
    (hi : wramPhys svbk addr < wram.size) :
    wramRead (wramWrite wram svbk addr v) svbk addr = v := by
  unfold wramRead wramWrite
  exact bget_bset_same _ _ _ hi

/-- Writes through one WRAM bank are invisible through another bank. -/
theorem wram_isolation (wram : ByteArray) (svbk svbk' : UInt8)
    (addr : Nat) (v : UInt8)
    (hlo : 0xD000 ≤ addr) (hhi : addr < 0xE000)
    (hne : wramBank svbk ≠ wramBank svbk')
    (h1 : wramPhys svbk addr < wram.size)
    (h2 : wramPhys svbk' addr < wram.size) :
    wramRead (wramWrite wram svbk addr v) svbk' addr =
      wramRead wram svbk' addr := by
  have hb1 := wramBank_bounds svbk
  have hb2 := wramBank_bounds svbk'
  have hne' : wramPhys svbk addr ≠ wramPhys svbk' addr := by
    unfold wramPhys wramBankSize
    have e1 : ¬ addr < 0xD000 := by omega
    simp only [e1, ite_false]
    omega
  unfold wramRead wramWrite
  exact bget_bset_ne _ _ _ _ h1 h2 hne'

/-- Reading back a banked VRAM write. -/
theorem vram_rw (vram : ByteArray) (vbk : UInt8) (addr : Nat) (v : UInt8)
    (hi : vramPhys vbk addr < vram.size) :
    vramRead (vramWrite vram vbk addr v) vbk addr = v := by
  unfold vramRead vramWrite
  exact bget_bset_same _ _ _ hi

/-- Writes through one VRAM bank are invisible through the other. -/
theorem vram_isolation (vram : ByteArray) (vbk vbk' : UInt8)
    (addr : Nat) (v : UInt8)
    (hne : vramBank vbk ≠ vramBank vbk')
    (h1 : vramPhys vbk addr < vram.size)
    (h2 : vramPhys vbk' addr < vram.size) :
    vramRead (vramWrite vram vbk addr v) vbk' addr =
      vramRead vram vbk' addr := by
  have hb1 := vramBank_lt2 vbk
  have hb2 := vramBank_lt2 vbk'
  have hne' : vramPhys vbk addr ≠ vramPhys vbk' addr := by
    unfold vramPhys vramBankSize
    omega
  unfold vramRead vramWrite
  exact bget_bset_ne _ _ _ _ h1 h2 hne'

/-! ## Palette RAM -/

theorem palFresh_size : palFresh.size = 32 := by decide

/-- Fresh palettes read back white. -/
theorem palFresh_get (i : Nat) (hi : i < 32) :
    palGet palFresh i = 0x7FFF := by
  have hsz : palFresh.size = 32 := by decide
  have hlist : palFresh.toList = List.replicate 32 (0x7FFF : UInt16) := rfl
  unfold palGet
  split
  next h =>
    have hlen : i < palFresh.toList.length := by
      rw [hlist, List.length_replicate]
      omega
    have hL : palFresh.toList[i]'hlen = 0x7FFF := List.getElem_replicate _
    exact (Array.getElem_toList hlen).symm.trans hL
  next _ => rfl

/-- Writing then reading a palette entry round-trips. -/
theorem palGet_set_same (pal : Array UInt16) (i : Nat) (c : UInt16)
    (hi : i < pal.size) :
    palGet (palSet pal i c) i = c := by
  simp [palSet, palGet, hi]

/-- Writes never clobber another palette entry. -/
theorem palGet_set_ne (pal : Array UInt16) (i j : Nat) (c : UInt16)
    (hi : i < pal.size) (hj : j < pal.size) (hne : i ≠ j) :
    palGet (palSet pal i c) j = palGet pal j := by
  simp [palSet, palGet, hi, hj, hne]

/-- A byte write is visible to reads of a different entry. -/
theorem palWriteByte_other (pal : Array UInt16) (idx j : Nat) (v : UInt8)
    (hi : idx / 2 < pal.size) (hj : j < pal.size)
    (hne : idx / 2 ≠ j) :
    palGet (palWriteByte pal idx v) j = palGet pal j := by
  unfold palWriteByte
  exact palGet_set_ne _ _ _ _ hi hj hne

/-! ## Palette auto-increment -/

/-- Without the auto-increment bit the index is untouched. -/
theorem palAutoInc_noInc (reg : UInt8) (h : bitGet reg 7 = false) :
    palAutoInc reg = reg := by
  simp [palAutoInc, h]

theorem palAutoInc_off : palAutoInc 0x05 = 0x05 := by decide

theorem palAutoInc_step : palAutoInc 0x80 = 0x81 := by decide

theorem palAutoInc_wrap : palAutoInc 0xBF = 0x80 := by decide

/-! ## BGR555 → ARGB888 -/

theorem cgbColor_black : cgbColor 0 = 0xFF000000 := by decide

theorem cgbColor_white : cgbColor 0x7FFF = 0xFFFFFFFF := by decide

theorem cgbColor_red : cgbColor 0x001F = 0xFFFF0000 := by decide

theorem cgbColor_green : cgbColor 0x03E0 = 0xFF00FF00 := by decide

theorem cgbColor_blue : cgbColor 0x7C00 = 0xFF0000FF := by decide

/-! ## HDMA length + status -/

/-- Transfer length is always 16..2048 bytes. -/
theorem totalLen_bounds (v : UInt8) :
    16 ≤ HdmaState.totalLen v ∧ HdmaState.totalLen v ≤ 2048 := by
  unfold HdmaState.totalLen
  have hmod : v.toNat % 128 < 128 := by omega
  omega

theorem totalLen_zero : HdmaState.totalLen 0 = 16 := by decide

theorem totalLen_max : HdmaState.totalLen 0x7F = 2048 := by decide

theorem totalLen_wrap : HdmaState.totalLen 0xFF = 2048 := by decide

/-- Idle HDMA reads back done (`0x80`). -/
theorem statusReg_idle : HdmaState.statusReg {} = 0x80 := by decide

/-- One active block reads back `0x00`. -/
theorem statusReg_active :
    HdmaState.statusReg { remaining := 16, active := true } = 0x00 := by
  decide

end GB
