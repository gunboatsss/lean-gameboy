/-
  LeanAGB.Proofs.Ppu — scanline-counter invariants, frame geometry,
  VBlank/frame-wrap edge instances, and mode-3 render contracts
  (scanline/frame size preservation, pixel color instances).
-/
import LeanAGB.Proofs.Basic
import LeanAGB.Bus
import LeanAGB.Emu

namespace AGB

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

-- ── Frame geometry ──

theorem frameGeometry :
    AGB_CYCLES_PER_LINE * AGB_LINES_PER_FRAME = AGB_CYCLES_PER_FRAME := by
  decide

theorem agbPixels : agbWidth * agbHeight = 38400 := by
  decide

-- ── Scanline counter invariant: VCOUNT always names a real line ──

theorem stepPpu_vcount_lt (s : AGBState) (n : Nat)
    (h2 : s.ppu.vcount.toNat < 228) :
    (stepPpu s n).ppu.vcount.toNat < 228 := by
  unfold stepPpu
  dsimp only
  split
  · exact h2
  · split
    · show (160 : UInt16).toNat < 228
      rw [u16_160_toNat]
      decide
    · split
      · show (0 : UInt16).toNat < 228
        rw [u16_0_toNat]
        decide
      · have hlt : s.ppu.vcount.toNat + 1 < 65536 := by omega
        have hL : AGB_LINES_PER_FRAME = 228 := by rfl
        rw [w16_toNat, Nat.mod_eq_of_lt hlt]
        omega

-- ── VBlank + frame-wrap edge instances ──

/-- End of line 159, one dot before VBlank. -/
def ppuPreVBlank : AGBState :=
  { ({} : AGBState) with ppu := { dots := 1231, vcount := 159 } }

theorem vblank_fires : ((stepPpu ppuPreVBlank 1).irq.if_ &&& 1) = 1 := by
  decide

theorem vblank_line : (stepPpu ppuPreVBlank 1).ppu.vcount = 160 := by
  decide

/-- End of the last line; the next dot wraps the frame. -/
def ppuPreWrap : AGBState :=
  { ({} : AGBState) with ppu := { dots := 1231, vcount := 227, frame := 41 } }

theorem frame_wraps : (stepPpu ppuPreWrap 1).ppu.frame = 42 := by
  decide

theorem vcount_wraps : (stepPpu ppuPreWrap 1).ppu.vcount = 0 := by
  decide

-- ── Mode-3 render contracts ──

theorem agbPlot_size (fb : Array UInt32) (x y : Nat) (c : UInt32) :
    (agbPlot fb x y c).size = fb.size := by
  unfold agbPlot
  split <;> simp

theorem mode3BlitLine_size (vram : ByteArray) (y : Nat) (fb : Array UInt32) (k : Nat) :
    (mode3BlitLine vram y fb k).size = fb.size := by
  induction k generalizing fb with
  | zero => rfl
  | succ k ih => simp [mode3BlitLine, ih, agbPlot_size]

theorem renderMode3_size (vram : ByteArray) (fb : Array UInt32) (j : Nat) :
    (renderMode3 vram fb j).size = fb.size := by
  have step : ∀ (xs : List Nat) (acc : Array UInt32),
      ((((xs.foldl fun acc k => mode3BlitLine vram k acc agbWidth)) acc).size
        = acc.size) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons k xs ih =>
      intro acc
      simp only [List.foldl_cons, ih, mode3BlitLine_size]
  unfold renderMode3
  exact step _ _

/-- One red pixel at the origin of a tiny VRAM. -/
def pxRed : ByteArray := ByteArray.mk #[0x1F, 0x00]

theorem mode3_red : mode3Pixel pxRed 0 0 = 0xFFFF0000 := by
  decide

/-- Mode-0 scene: palette {black, red}, tile0 solid idx1, map tile 0. -/
def pxPal : ByteArray := ByteArray.mk #[0, 0, 0x1F, 0]

def pxVram : ByteArray :=
  let blank := ByteArray.mk (Array.mk (List.replicate 0x960 (0 : UInt8)))
  let t := (List.range 32).foldl (fun b i => b.set! i 0x11) blank
  -- map col 0 = tile 0 (red), col 1 = tile 1 (zero tile → backdrop);
  -- block-1 row 5 col 0 = tile 1 (size-2 bottom-half target)
  (((t.set! 0x800 0).set! 0x801 0).set! 0x802 1).set! 0x940 1

def pxPpu : AgbPpu :=
  { dispcnt := 0x0100, bgcnt := #[0x0100, 0, 0, 0] }

theorem mode0_red : mode0Pixel pxPpu (palARGB pxPal) pxVram 0 0 = 0xFFFF0000 := by
  decide

theorem mode0_next_tile_backdrop :
    mode0Pixel pxPpu (palARGB pxPal) pxVram 0 8 = 0xFF000000 := by
  decide

theorem mode0_scroll :
    mode0Pixel { pxPpu with bghofs := #[8, 0, 0, 0] } (palARGB pxPal) pxVram 0 0
      = 0xFF000000 := by
  decide

theorem mode0_disabled_backdrop :
    mode0Pixel {} (palARGB pxPal) pxVram 0 0 = 0xFF000000 := by
  decide

/-- Size-2 (256×512) bottom half reads SC1 (+0x800), not SC2. -/
theorem mode0_size2_bottom :
    mode0Pixel { pxPpu with bgcnt := #[0x8000, 0, 0, 0] } (palARGB pxPal) pxVram 300 0
      = 0xFF000000 := by
  decide

/-- Tiny VRAM: red pixel 0, white pixel 1, white (OOB=`0xFF`) elsewhere. -/
def pxLine : ByteArray := ByteArray.mk #[0x1F, 0x00, 0xFF, 0x7F]

/-- A full scanline blit preserves the white background except pixel 0. -/
def whiteLine : Array UInt32 := Array.replicate agbWidth (0xFFFFFFFF : UInt32)

theorem mode3_line_first_pixel :
    (mode3BlitLine pxLine 0 whiteLine 240).getD 0 0 = 0xFFFF0000 := by
  decide

theorem mode3_line_second_stays_white :
    (mode3BlitLine pxLine 0 whiteLine 240).getD 1 0 = 0xFFFFFFFF := by
  decide

-- ── Mode-3 refresh preserves everything but pixels ──

theorem renderFrame_cycles (s : AGBState) : (renderFrame s).cycles = s.cycles := by
  unfold renderFrame
  repeat (first | split | rfl)

theorem mode4BlitLine_size (palT : Array UInt32) (vram : ByteArray) (page y : Nat)
    (fb : Array UInt32) (k : Nat) :
    (mode4BlitLine palT vram page y fb k).size = fb.size := by
  induction k generalizing fb with
  | zero => rfl
  | succ k ih => simp [mode4BlitLine, ih, agbPlot_size]

theorem renderMode4_size (pal vram : ByteArray) (page : Nat)
    (fb : Array UInt32) (j : Nat) :
    (renderMode4 pal vram page fb j).size = fb.size := by
  have step : ∀ (xs : List Nat) (pt : Array UInt32) (acc : Array UInt32),
      ((((xs.foldl fun acc k => mode4BlitLine pt vram page k acc agbWidth)) acc).size
        = acc.size) := by
    intro xs pt
    induction xs with
    | nil => intro acc; rfl
    | cons k xs ih =>
      intro acc
      simp only [List.foldl_cons, ih, mode4BlitLine_size]
  unfold renderMode4
  simp only []
  exact step _ _ _

theorem mode5BlitLine_size (vram : ByteArray) (page y : Nat)
    (fb : Array UInt32) (k : Nat) :
    (mode5BlitLine vram page y fb k).size = fb.size := by
  induction k generalizing fb with
  | zero => rfl
  | succ k ih => simp [mode5BlitLine, ih, agbPlot_size]

theorem renderMode5_size (pal vram : ByteArray) (page : Nat)
    (fb : Array UInt32) :
    (renderMode5 pal vram page fb).size = fb.size := by
  unfold renderMode5
  simp only []
  have step : ∀ (xs : List Nat) (acc : Array UInt32),
      ((((xs.foldl fun acc k => mode5BlitLine vram page k acc mode5Width)) acc).size
        = acc.size) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons k xs ih =>
      intro acc
      simp only [List.foldl_cons, ih, mode5BlitLine_size]
  -- backdrop fill preserves size (agbPlot no-ops out of bounds)
  have fill : ∀ (xs : List Nat) (acc : Array UInt32),
      ((((xs.foldl fun acc i =>
        agbPlot acc (i % agbWidth) (i / agbWidth)
          (bgr555ToARGB (bget16LE pal 0)))) acc).size
        = acc.size) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons k xs ih =>
      intro acc
      simp only [List.foldl_cons, ih, agbPlot_size]
  simp [fill, step]

-- NOTE: page-1 pixels (file offset 0xA000) are pinned natively in
-- agb-test; kernel `decide` over 40K-deep array construction/indexing
-- exceeds any reasonable `maxRecDepth`.
/-- Mode-4 scene: index 5 → green at the page-0 origin. -/
def m4Pal : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0, 0, 0x7C, 0, 0, 0, 0, 0xE0, 0x03]

def m4Vram : ByteArray := ByteArray.mk #[5]

theorem mode4_page0_green : mode4Pixel (palARGB m4Pal) m4Vram 0 0 0 = 0xFF00FF00 := by
  decide

/-- Mode-5 scene: red at the page-0 origin. -/
def m5Vram : ByteArray := ByteArray.mk #[0x1F, 0]

theorem mode5_page0_red : mode5Pixel m5Vram 0 0 0 = 0xFFFF0000 := by
  decide

theorem mode0LineLoop_size (ppu : AgbPpu) (palT : Array UInt32)
    (vram : ByteArray) (sps : List AgbSprite) (spans : Array BgSpan)
    (y : Nat) (fb : Array UInt32) (k : Nat) :
    (mode0LineLoop ppu palT vram sps spans y fb k).size = fb.size := by
  induction k generalizing fb with
  | zero => rfl
  | succ k ih => simp [mode0LineLoop, ih, agbPlot_size]

theorem mode0LineLoopCfg_size (bc : BlendCfg) (palT : Array UInt32)
    (vram : ByteArray) (objs : Array (Option Cand)) (spans : Array BgSpan)
    (y : Nat) (fb : Array UInt32) (k : Nat) :
    (mode0LineLoopCfg bc palT vram objs spans y fb k).size = fb.size := by
  induction k generalizing fb with
  | zero => rfl
  | succ k ih => simp [mode0LineLoopCfg, ih, agbPlot_size]

theorem mode0BlitLine_size (ppu : AgbPpu) (palT : Array UInt32)
    (vram : ByteArray) (parsed : Array (Option AgbSprite)) (y : Nat)
    (fb : Array UInt32) (k : Nat) :
    (mode0BlitLine ppu palT vram parsed y fb k).size = fb.size := by
  unfold mode0BlitLine
  exact mode0LineLoopCfg_size _ _ _ _ _ _ _ k

theorem renderMode0_size (ppu : AgbPpu) (pal vram oam : ByteArray)
    (fb : Array UInt32) (j : Nat) :
    (renderMode0 ppu pal vram oam fb j).size = fb.size := by
  have step : ∀ (xs : List Nat) (pt : Array UInt32)
      (parsed : Array (Option AgbSprite)) (acc : Array UInt32),
      ((((xs.foldl fun acc k => mode0BlitLine ppu pt vram parsed k acc agbWidth)) acc).size
        = acc.size) := by
    intro xs pt parsed
    induction xs with
    | nil => intro acc; rfl
    | cons k xs ih =>
      intro acc
      simp only [List.foldl_cons, ih, mode0BlitLine_size]
  unfold renderMode0
  simp only []
  exact step _ _ _ _

/-- The per-line entry point is definitionally the parse-table filter
    (same order, same membership on every line, by construction). -/
theorem spritesOnLine_eq_parsed (oam : ByteArray) (y : Nat) :
    spritesOnLine oam y = spritesOnLineParsed (parseOam oam) y := by
  rfl

/-- Sprite scene: entry 0 = 8×8 white tile 0 at (4,4), rest parked at Y=160.
    OBJ palette 0: {black, _, white}; tile 0 at VRAM+0x10000 solid idx2. -/
def sprOam : ByteArray :=
  let blank := ByteArray.mk (Array.mk (List.replicate 0x400 (0 : UInt8)))
  let parked := (List.range 127).foldl (fun b i => b.set! (8 * (i + 1)) 160) blank
  (parked.set! 0 4).set! 2 4

def sprVram : ByteArray :=
  let blank := ByteArray.mk (Array.mk (List.replicate 0x10020 (0 : UInt8)))
  (List.range 32).foldl (fun b i => b.set! (0x10000 + i) 0x22) blank

def sprPal : ByteArray := ByteArray.mk #[0, 0, 0, 0, 0xFF, 0x7F]

def sprPpu : AgbPpu := { dispcnt := 0x1000 }

theorem sprite_parse_origin :
    parseAgbSprite sprOam 0
      = some { x := 4, y := 4, w := 8, h := 8, tile := 0, prio := 0,
               pal := 0, is8 := false, hflip := false, vflip := false,
               semi := false } := by
  decide

theorem sprite_parked_y160 :
    parseAgbSprite sprOam 1
      = some { x := 0, y := 160, w := 8, h := 8, tile := 0, prio := 0,
               pal := 0, is8 := false, hflip := false, vflip := false,
               semi := false } := by
  decide

-- ── Sprite tile-number mapping (GBATEK 1D/2D, Tonc fig 8.2) ──

def tileSp4 : AgbSprite :=
  { x := 0, y := 0, w := 16, h := 16, tile := 0, prio := 0, pal := 0,
    is8 := false, hflip := false, vflip := false }

def tileSp8 : AgbSprite :=
  { x := 0, y := 0, w := 16, h := 16, tile := 0, prio := 0, pal := 0,
    is8 := true, hflip := false, vflip := false }

theorem tileNum_4bpp_2d : spriteTileNum tileSp4 false 1 1 = 33 := by decide

theorem tileNum_8bpp_2d_row : spriteTileNum tileSp8 false 0 1 = 32 := by decide

theorem tileNum_8bpp_2d_col : spriteTileNum tileSp8 false 1 1 = 34 := by decide

theorem tileNum_8bpp_2d_mask :
    spriteTileNum { tileSp8 with tile := 1 } false 0 1 = 32 := by decide

theorem tileNum_8bpp_1d : spriteTileNum tileSp8 true 1 1 = 6 := by decide

-- ── Sprite Y-wraparound rows (`(y + 256 - spY) % 256 < h`) ──

theorem spriteRow_plain : spriteRow 10 8 12 = some 2 := by decide

theorem spriteRow_before : spriteRow 10 8 5 = none := by decide

theorem spriteRow_wrap_top : spriteRow 250 16 0 = some 6 := by decide

theorem spriteRow_wrap_mid : spriteRow 250 16 8 = some 14 := by decide

theorem spriteRow_wrap_gap : spriteRow 250 16 100 = none := by decide

theorem spriteRow_parked : spriteRow 160 8 0 = none := by decide

/-- No-wrap equivalence: when the sprite can't reach the wrap boundary,
    the new row mapping coincides with the old bounds check
    (`spY ≤ y < spY + h`, row `y - spY`) — so every non-wrapping sprite
    renders exactly as before (cf. title-identical dumps). -/
theorem spriteRow_nowrap (spY h y : Nat) (hnw : spY + h ≤ 256) (hy : y < 256) :
    spriteRow spY h y
      = if spY ≤ y ∧ y < spY + h then some (y - spY) else none := by
  by_cases hle : spY ≤ y
  · have hmod : (y + 256 - spY) % 256 = y - spY := by omega
    simp only [spriteRow, hmod]
    by_cases hlt : y - spY < h
    · have hc : spY ≤ y ∧ y < spY + h := by omega
      simp only [hlt, hc, ite_true, and_self]
    · have hc : ¬(spY ≤ y ∧ y < spY + h) := by
        rintro ⟨h1, h2⟩
        omega
      simp only [hlt, hc, if_false]
  · have hmod : (y + 256 - spY) % 256 = y + 256 - spY := by omega
    simp only [spriteRow, hmod]
    have hc : ¬(spY ≤ y ∧ y < spY + h) := fun ⟨h1, _⟩ => hle h1
    have hlt : ¬(y + 256 - spY < h) := by omega
    simp only [hlt, hc, ite_false]

-- ── Blend math pins (GBATEK coefficients, /16 fixed point) ──

theorem mix_half_red_blue : mixARGB 0xFFFF0000 0xFF0000FF 8 8 = 0xFF7F007F := by
  decide

theorem mix_clamp_white : mixARGB 0xFFFFFFFF 0xFFFFFFFF 16 16 = 0xFFFFFFFF := by
  decide

theorem brighten_half_red : fxAdjust 0xFFFF0000 true 8 = 0xFFFF7F7F := by
  decide

theorem darken_half_red : fxAdjust 0xFFFF0000 false 8 = 0xFF800000 := by
  decide

theorem brighten_zero_noop : fxAdjust 0xFF123456 true 0 = 0xFF123456 := by
  decide

-- NOTE: full sprite-pixel checks (OBJ tile reads at VRAM+0x10000)
-- live in agb-test natively: kernel `decide` over 65K-deep array
-- indexing exceeds any reasonable `maxRecDepth`. The kernel pins
-- parsing, parking, misses and all BG pixels; native covers colors.
theorem sprite_miss_backdrop :
    framePixel sprPpu (palARGB sprPal) sprVram (spritesOnLine sprOam 4)
      #[bgSpan sprPpu 0 4, bgSpan sprPpu 1 4, bgSpan sprPpu 2 4,
        bgSpan sprPpu 3 4] 4 12
      = 0xFF000000 := by
  decide

-- ── Render memo contracts ──

/-- The view keeps DISPCNT but drops VCOUNT/dots/frame. -/
theorem renderView_project :
    renderView { dispcnt := 3, vcount := 99, dots := 1000, frame := 7 }
      = { dispcnt := 3 } := by decide

/-- Full key match: the hit returns the cached framebuffer. -/
theorem memoRenderFrame_hit (s : AGBState) (m : RenderMemo)
    (hv : m.valid = true)
    (hview : (m.view == renderView s.ppu) = true)
    (hpal : (m.pal == s.pal) = true)
    (hvram : (m.vram == s.vram) = true)
    (hoam : (m.oam == s.oam) = true) :
    (memoRenderFrame s m).1.fb = m.fb := by
  unfold memoRenderFrame
  simp [hv, hview, hpal, hvram, hoam]

/-- Cold memo: the miss renders and validates. -/
theorem memoRenderFrame_miss (s : AGBState) (m : RenderMemo)
    (hv : m.valid = false) :
    (memoRenderFrame s m).1 = renderFrame s
      ∧ (memoRenderFrame s m).2.valid = true := by
  unfold memoRenderFrame
  simp [hv]

/-! ## Unimplemented modes 1/2: documented no-ops -/

/-- Mode 1 keeps the previous framebuffer. -/
theorem renderFrame_mode1 (s : AGBState)
    (hblank : ((s.ppu.dispcnt.toNat >>> 7) &&& 1) = 0)
    (hmode : (s.ppu.dispcnt.toNat &&& 7) = 1) :
    (renderFrame s).fb = s.fb := by
  simp [renderFrame, hblank, hmode]

/-- Mode 2 keeps the previous framebuffer. -/
theorem renderFrame_mode2 (s : AGBState)
    (hblank : ((s.ppu.dispcnt.toNat >>> 7) &&& 1) = 0)
    (hmode : (s.ppu.dispcnt.toNat &&& 7) = 2) :
    (renderFrame s).fb = s.fb := by
  simp [renderFrame, hblank, hmode]

/-- Forced blank fills white. -/
theorem renderFrame_blank (s : AGBState)
    (hblank : ((s.ppu.dispcnt.toNat >>> 7) &&& 1) = 1) :
    (renderFrame s).fb = renderBlank s.fb := by
  simp [renderFrame, hblank]

/-- Rendering never touches PPU registers. -/
theorem renderFrame_ppu (s : AGBState) : (renderFrame s).ppu = s.ppu := by
  unfold renderFrame
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · rfl

/-! ## Blank-fill sizing -/

/-- Plotting preserves the framebuffer size over any index list. -/
theorem foldPlot_size (l : List Nat) (fb : Array UInt32) (c : UInt32) :
    ((l.foldl (fun acc i => agbPlot acc (i % agbWidth) (i / agbWidth) c) fb).size
      = fb.size) := by
  induction l generalizing fb with
  | nil => rfl
  | cons _ t ih =>
    simp only [List.foldl_cons, ih, agbPlot_size]

/-- Blank fill preserves the framebuffer size. -/
theorem renderBlank_size (fb : Array UInt32) :
    (renderBlank fb).size = fb.size :=
  foldPlot_size _ _ _

end AGB
