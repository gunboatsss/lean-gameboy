/- LeanAGB.Ppu — scanline counter + lazy frame renderer.
   Geometry: 228 lines × 1232 cycles; 160 visible lines of 240 px.
   Mode 0: 4 text BGs (4/8bpp tiles, flips, per-layer priority) plus
   non-affine OBJs (all sizes, 1D/2D mapping, OAM-order tiebreaks;
   semi-transparent renders as normal).
   Mode 3: 240×160 16-bit BGR555 bitmap at the start of VRAM.
   Mode 4: 240×160 paletted bitmap, two 40K pages (DISPCNT.4 selects).
   Mode 5: 160×128 16-bit bitmap at top-left, two 40K pages, backdrop
   elsewhere.
   Modes 1/2, affine OBJs, OBJ window, mosaic, blend: open gaps. -/
import LeanAGB.Basic

namespace AGB
def AGB_CYCLES_PER_LINE : Nat := 1232
def AGB_LINES_PER_FRAME : Nat := 228
def AGB_CYCLES_PER_FRAME : Nat := 280896  -- 16.78 MHz / ~59.73 Hz
def agbWidth : Nat := 240
def agbHeight : Nat := 160
structure AgbPpu where
  dispcnt : UInt16 := 0
  dispstat : UInt16 := 0
  vcount : UInt16 := 0
  dots : Nat := 0
  frame : Nat := 0
  bgcnt : Array UInt16 := Array.replicate 4 0
  bghofs : Array UInt16 := Array.replicate 4 0
  bgvofs : Array UInt16 := Array.replicate 4 0
  bldcnt : UInt16 := 0
  bldalpha : UInt16 := 0
  bldy : UInt16 := 0
deriving DecidableEq, Repr

/-- Render-relevant PPU registers: every `AgbPpu` field the pixel path
    reads (DISPCNT selects mode/page, BG regs feed the layer math,
    blend regs feed the compositor). Dots/VCOUNT/DISPSTAT/frame never
    affect pixels, so they are excluded (VCOUNT advances every line —
    including it would disable the render memo entirely). -/
structure RenderView where
  dispcnt : UInt16 := 0
  bgcnt : Array UInt16 := Array.replicate 4 0
  bghofs : Array UInt16 := Array.replicate 4 0
  bgvofs : Array UInt16 := Array.replicate 4 0
  bldcnt : UInt16 := 0
  bldalpha : UInt16 := 0
  bldy : UInt16 := 0
deriving DecidableEq, Repr

/-- Project the render-relevant registers (the memo key's PPU part). -/
def renderView (ppu : AgbPpu) : RenderView :=
  { dispcnt := ppu.dispcnt, bgcnt := ppu.bgcnt, bghofs := ppu.bghofs,
    bgvofs := ppu.bgvofs, bldcnt := ppu.bldcnt, bldalpha := ppu.bldalpha,
    bldy := ppu.bldy }

/-- Plot one pixel (no-op out of bounds; mirrors GB `fbSet`). -/
@[inline] def agbPlot (fb : Array UInt32) (x y : Nat) (c : UInt32) : Array UInt32 :=
  if x < agbWidth && y < agbHeight then fb.set! (y * agbWidth + x) c
  else fb

/-- Precomputed ARGB palette (512 entries over pal bytes; table
    index = byte-offset / 2, so BG indices land 0..255 and OBJ
    palettes 256..511). Built once per render instead of converting
    per pixel (each conversion is 3 divisions × ~100k pixels). -/
def palARGB (pal : ByteArray) : Array UInt32 :=
  Array.mk ((List.range 512).map (fun i => bgr555ToARGB (bget16LE pal (i * 2))))

/-- Mode 3 pixel: 16-bit BGR555 bitmap at the start of VRAM. -/
def mode3Pixel (vram : ByteArray) (x y : Nat) : UInt32 :=
  bgr555ToARGB (bget16LE vram ((y * agbWidth + x) * 2))

/-- Blit one mode-3 scanline (`fuel = agbWidth` covers x = 239..0). -/
def mode3BlitLine (vram : ByteArray) (y : Nat) (fb : Array UInt32) : Nat → Array UInt32
  | 0 => fb
  | fuel + 1 =>
    let x := agbWidth - (fuel + 1)
    mode3BlitLine vram y (agbPlot fb x y (mode3Pixel vram x y)) fuel

/-- Render `lines` mode-3 scanlines (top-down) over the framebuffer. -/
def renderMode3 (vram : ByteArray) (fb : Array UInt32) (lines : Nat) : Array UInt32 :=
  (List.range lines).foldl (fun fb k => mode3BlitLine vram k fb agbWidth) fb

-- ── Modes 4/5 bitmaps (two 0xA000-spaced pages, DISPCNT.4 selects) ──

def mode4Width : Nat := 240
def mode5Width : Nat := 160
def mode5Height : Nat := 128

/-- Mode-4 pixel: paletted index from the selected page (table). -/
def mode4Pixel (palT : Array UInt32) (vram : ByteArray) (page x y : Nat) :
    UInt32 :=
  palT.getD (bget vram (page * 0xA000 + y * 240 + x)).toNat 0xFFFFFFFF

/-- Blit one mode-4 scanline. -/
def mode4BlitLine (palT : Array UInt32) (vram : ByteArray) (page y : Nat)
    (fb : Array UInt32) : Nat → Array UInt32
  | 0 => fb
  | fuel + 1 =>
    let x := mode4Width - (fuel + 1)
    mode4BlitLine palT vram page y (agbPlot fb x y (mode4Pixel palT vram page x y)) fuel

/-- Render `lines` mode-4 scanlines (top-down) over the framebuffer. -/
def renderMode4 (pal vram : ByteArray) (page : Nat) (fb : Array UInt32)
    (lines : Nat) : Array UInt32 :=
  let palT := palARGB pal
  (List.range lines).foldl
    (fun fb k => mode4BlitLine palT vram page k fb agbWidth) fb

/-- Mode-5 pixel: direct BGR555 from the selected page. -/
def mode5Pixel (vram : ByteArray) (page x y : Nat) : UInt32 :=
  bgr555ToARGB (bget16LE vram (page * 0xA000 + (y * mode5Width + x) * 2))

/-- Blit one mode-5 scanline (160 px at the left edge). -/
def mode5BlitLine (vram : ByteArray) (page y : Nat) (fb : Array UInt32) :
    Nat → Array UInt32
  | 0 => fb
  | fuel + 1 =>
    let x := mode5Width - (fuel + 1)
    mode5BlitLine vram page y (agbPlot fb x y (mode5Pixel vram page x y)) fuel

/-- Render a mode-5 frame: backdrop fill, then the 160×128 image. -/
def renderMode5 (pal vram : ByteArray) (page : Nat) (fb : Array UInt32) : Array UInt32 :=
  let back := bgr555ToARGB (bget16LE pal 0)
  let fb := (List.range (agbWidth * agbHeight)).foldl
    (fun fb i => agbPlot fb (i % agbWidth) (i / agbWidth) back) fb
  (List.range mode5Height).foldl
    (fun fb k => mode5BlitLine vram page k fb mode5Width) fb

-- ── Mode 0 text backgrounds ──
-- GBATEK "LCD I/O BG Control": tile/map BG modes. One pixel of layer
-- `ch` at frame `(x, y)`; `none` = transparent (index 0).

/-- Priority (bits 0-1) of a BG layer. -/
def layerPrio (ppu : AgbPpu) (ch : Nat) : Nat :=
  (ppu.bgcnt.getD ch 0).toNat &&& 0x3

/-- Per-scanline BG layer setup: everything `bgLinePixel` needs
    that doesn't vary with `x` (hoisted out of the pixel loop —
    240× fewer BG register reads and map-geometry recomputes). -/
structure BgSpan where
  en : Bool := false
  prio : Nat := 0
  charBase : Nat := 0
  scrBase : Nat := 0
  size : Nat := 0
  is8 : Bool := false
  w : Nat := 256
  h : Nat := 256
  hofs : Nat := 0
  sy : Nat := 0
  ty : Nat := 0
  blkRow : Nat := 0
deriving DecidableEq, Repr

def bgSpan (ppu : AgbPpu) (ch y : Nat) : BgSpan :=
  let cnt := (ppu.bgcnt.getD ch 0).toNat
  let size := (cnt >>> 14) &&& 0x3
  let h := if size == 2 || size == 3 then 512 else 256
  let sy := (y + (ppu.bgvofs.getD ch 0).toNat) % h
  let blkY := if size == 2 || size == 3 then sy / 256 else 0
  { en := ((ppu.dispcnt.toNat >>> (8 + ch)) &&& 1) == 1
    prio := cnt &&& 0x3
    charBase := ((cnt >>> 2) &&& 0x3) * 0x4000
    scrBase := ((cnt >>> 8) &&& 0x1F) * 0x800
    size := size
    is8 := ((cnt >>> 7) &&& 1) == 1
    w := if size == 1 || size == 3 then 512 else 256
    h := h
    hofs := (ppu.bghofs.getD ch 0).toNat
    sy := sy
    ty := (sy % 256) / 8
    blkRow :=
      if size == 3 then blkY * 2 else if size == 2 then blkY else 0 }

@[inline] def bgLinePixel (sp : BgSpan) (palT : Array UInt32) (vram : ByteArray)
    (x : Nat) : Option UInt32 :=
  if !sp.en then none
  else
    let sx := (x + sp.hofs) % sp.w
    let blkX := if sp.size == 1 || sp.size == 3 then sx / 256 else 0
    let tx := (sx % 256) / 8
    let blk := sp.blkRow + (if sp.size == 1 || sp.size == 3 then blkX else 0)
    let mapAddr := sp.scrBase + blk * 0x800 + (sp.ty * 32 + tx) * 2
    let entry := (bget16LE vram mapAddr).toNat
    let tile := entry &&& 0x3FF
    let hf := ((entry >>> 10) &&& 1) == 1
    let vf := ((entry >>> 11) &&& 1) == 1
    let paln := (entry >>> 12) &&& 0xF
    let cx := if hf then 7 - (sx % 8) else sx % 8
    let cy := if vf then 7 - (sp.sy % 8) else sp.sy % 8
    if !sp.is8 then
      let b := (bget vram (sp.charBase + tile * 32 + cy * 4 + cx / 2)).toNat
      let idx := if cx % 2 == 0 then b &&& 0xF else (b >>> 4) &&& 0xF
      if idx == 0 then none
      else some (palT.getD (paln * 16 + idx) 0xFFFFFFFF)
    else
      let idx := (bget vram (sp.charBase + tile * 64 + cy * 8 + cx)).toNat
      if idx == 0 then none
      else some (palT.getD idx 0xFFFFFFFF)

/-- Priority/layer scan order (prio-major, layer-minor), hoisted so
    per-pixel scans never build it (38,400 builds/frame otherwise). -/
def prioLayerOrder : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
   (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

/-- Mode-0 background scan: lowest (priority, layer) hit, if any. -/
def mode0Scan (ppu : AgbPpu) (palT : Array UInt32) (vram : ByteArray) (y x : Nat) :
    Option (UInt32 × Nat) :=
  prioLayerOrder.foldl (fun (acc : Option (UInt32 × Nat)) (pc : Nat × Nat) =>
    match acc with
    | some _ => acc
    | none =>
      if layerPrio ppu pc.2 == pc.1 then
        match bgLinePixel (bgSpan ppu pc.2 y) palT vram x with
        | some c => some (c, pc.1)
        | none => none
      else none) none

/-- Mode-0 pixel: lowest (priority, layer) non-transparent BG wins,
    else the backdrop (palette entry 0). -/
def mode0Pixel (ppu : AgbPpu) (palT : Array UInt32) (vram : ByteArray)
    (y x : Nat) : UInt32 :=
  match mode0Scan ppu palT vram y x with
  | some (c, _) => c
  | none => palT.getD 0 0xFFFFFFFF

/-- Compositor candidate: (priority, tiebreak order, layer, color).
    BG order = layer+1 (layer decides ties); OBJ order 0 wins BG ties;
    backdrop order 6 loses everything. Layers match BLDCNT target bits:
    BG ch, OBJ = 4, backdrop = 5. -/
structure Cand where
  prio : Nat
  ord : Nat
  layer : Nat
  color : UInt32
  semi : Bool := false
deriving DecidableEq, Repr

@[inline] def better (a b : Cand) : Bool :=
  a.prio < b.prio || (a.prio == b.prio && a.ord < b.ord)

-- ── OBJs (non-affine; GBATEK "LCD OBJ") ──

/-- Parsed non-affine sprite (`none` = disabled/affine/window/prohibited).
    `x` is signed (9-bit wrap), `y` raw 0-255. -/
structure AgbSprite where
  x : Int
  y : Int
  w : Nat
  h : Nat
  tile : Nat
  prio : Nat
  pal : Nat
  is8 : Bool
  hflip : Bool
  vflip : Bool
  semi : Bool := false
deriving DecidableEq, Repr

/-- Shape × size → pixel dimensions (shape 3 prohibited). -/
def spriteDims (shape size : Nat) : Option (Nat × Nat) :=
  match shape, size with
  | 0, 0 => some (8, 8) | 0, 1 => some (16, 16)
  | 0, 2 => some (32, 32) | 0, 3 => some (64, 64)
  | 1, 0 => some (16, 8) | 1, 1 => some (32, 8)
  | 1, 2 => some (32, 16) | 1, 3 => some (64, 32)
  | 2, 0 => some (8, 16) | 2, 1 => some (8, 32)
  | 2, 2 => some (16, 32) | 2, 3 => some (32, 64)
  | _, _ => none

def parseAgbSprite (oam : ByteArray) (i : Nat) : Option AgbSprite :=
  let a0 := (bget16LE oam (i * 8)).toNat
  let a1 := (bget16LE oam (i * 8 + 2)).toNat
  let a2 := (bget16LE oam (i * 8 + 4)).toNat
  let rot := ((a0 >>> 8) &&& 1) == 1
  let dis := !rot && ((a0 >>> 9) &&& 1) == 1
  let mode := (a0 >>> 10) &&& 0x3
  if rot || dis || mode == 2 || mode == 3 then none
  else
    match spriteDims ((a0 >>> 14) &&& 0x3) ((a1 >>> 14) &&& 0x3) with
    | none => none
    | some (w, h) =>
      let ox := a1 &&& 0x1FF
      some { x := (if ox >= 256 then (ox : Int) - 512 else (ox : Int)),
             y := ((a0 &&& 0xFF : Nat) : Int),
             w := w, h := h, tile := a2 &&& 0x3FF,
             prio := (a2 >>> 10) &&& 0x3, pal := (a2 >>> 12) &&& 0xF,
             is8 := ((a0 >>> 13) &&& 1) == 1,
             hflip := ((a1 >>> 12) &&& 1) == 1,
             vflip := ((a1 >>> 13) &&& 1) == 1, semi := mode == 1 }

/-- Tile number of sprite cell (`tc`, `tr`) in 32-byte tile-ID units
    (numbering always follows s-tiles, even for d-tiles — Tonc).
    1D packs rows consecutively (`tw` = tiles per row); 2D rows stride
    32 IDs for both depths (GBATEK/Tonc fig 8.2b), columns stride 1
    (4bpp) or 2 (8bpp, whose base drops its low bit). -/
@[inline] def spriteTileNum (sp : AgbSprite) (oneD : Bool) (tc tr : Nat) : Nat :=
  let base := if sp.is8 then sp.tile &&& 0x3FE else sp.tile
  let step := if sp.is8 then 2 else 1
  let tw := sp.w / 8
  if oneD then base + (tr * tw + tc) * step
  else base + tr * 32 + tc * step

/-- Sprite row covering screen row `y`: rows map to
    `(spY + i) % 256`, so a sprite at Y=253 with height 32 shows its
    rows 3..31 at screen rows 0..28 (none = fully offscreen). -/
@[inline] def spriteRow (spY h y : Nat) : Option Nat :=
  let r := (y + 256 - spY) % 256
  if r < h then some r else none

/-- One sprite pixel (`none` = outside or transparent index 0).
    `oneD` = DISPCNT 1D mapping; OBJ tiles live at VRAM + 0x10000;
    OBJ palettes read from table entries 256..511. -/
@[inline] def spritePixel (sp : AgbSprite) (oneD : Bool) (palT : Array UInt32)
    (vram : ByteArray) (x y : Int) : Option UInt32 :=
  if x < sp.x || x >= sp.x + (sp.w : Int) then none
  else
    match spriteRow sp.y.toNat sp.h y.toNat with
    | none => none
    | some ry =>
      let rx := (x - sp.x).toNat
      let fx := if sp.hflip then sp.w - 1 - rx else rx
      let fy := if sp.vflip then sp.h - 1 - ry else ry
      let tc := fx / 8
      let tr := fy / 8
      let px := fx % 8
      let py := fy % 8
      let tn := spriteTileNum sp oneD tc tr
    let taddr := 0x10000 + tn * 32
    if !sp.is8 then
      let b := (bget vram (taddr + py * 4 + px / 2)).toNat
      let idx := if px % 2 == 0 then b &&& 0xF else (b >>> 4) &&& 0xF
      if idx == 0 then none
      else some (palT.getD (0x100 + sp.pal * 16 + idx) 0xFFFFFFFF)
    else
      let idx := (bget vram (taddr + py * 8 + px)).toNat
      if idx == 0 then none
      else some (palT.getD (0x100 + idx) 0xFFFFFFFF)

/-- All 128 OAM entries parsed once (per frame, not per line:
    the old per-line parse cost 20,480 parses/frame for identical bytes). -/
def parseOam (oam : ByteArray) : Array (Option AgbSprite) :=
  Array.mk ((List.range 128).map (parseAgbSprite oam))

/-- OAM-order sprite list covering scanline `y` from a pre-parsed table
    (Y-wraparound included: `spriteRow` decides per line; order = index
    order, exactly the old per-line parse-then-filter). -/
def spritesOnLineParsed (parsed : Array (Option AgbSprite)) (y : Nat) :
    List AgbSprite :=
  ((List.range 128).foldl (fun acc i =>
    match parsed.getD i none with
    | some sp =>
      match spriteRow sp.y.toNat sp.h y with
      | some _ => sp :: acc
      | none => acc
    | none => acc) []).reverse

/-- OAM-order sprite list covering scanline `y` (proof/test entry point;
    the hot loop filters a per-frame `parseOam` table instead). -/
def spritesOnLine (oam : ByteArray) (y : Nat) : List AgbSprite :=
  spritesOnLineParsed (parseOam oam) y

/-- All non-transparent BG hits, prio-major/layer-minor order. -/
def bgHits (ppu : AgbPpu) (palT : Array UInt32) (vram : ByteArray) (y x : Nat) :
    List Cand :=
  prioLayerOrder.filterMap (fun pc =>
    if layerPrio ppu pc.2 == pc.1 then
      match bgLinePixel (bgSpan ppu pc.2 y) palT vram x with
      | some c => some { prio := pc.1, ord := pc.2 + 1, layer := pc.2, color := c }
      | none => none
    else none)

/-- OAM-order scan for the first non-transparent sprite pixel
    (direct recursion: the per-pixel `foldl` closure allocated once per
    pixel, 38,400 closures/frame, for identical short-circuit order). -/
def objHitLoop (sps : List AgbSprite) (oneD : Bool) (palT : Array UInt32)
    (vram : ByteArray) (y x : Nat) : Option Cand :=
  match sps with
  | [] => none
  | sp :: rest =>
    match spritePixel sp oneD palT vram (x : Int) (y : Int) with
    | some c =>
      some { prio := sp.prio, ord := 0, layer := 4, color := c, semi := sp.semi }
    | none => objHitLoop rest oneD palT vram y x

/-- Topmost sprite hit from the pre-parsed scanline list (OAM-order
    first with index ≠ 0; priority is resolved in the merge, not here). -/
def objHit (ppu : AgbPpu) (palT : Array UInt32) (vram : ByteArray)
    (sps : List AgbSprite) (y x : Nat) : Option Cand :=
  if ((ppu.dispcnt.toNat >>> 12) &&& 1) == 0 then none
  else objHitLoop sps (((ppu.dispcnt.toNat >>> 6) &&& 1) == 1) palT vram y x

/-- Insert one candidate into a top-two accumulator (the exact step
    `topTwo` folds; kept separate so pixels never build lists). -/
@[inline] def topTwoInsert (acc : Option Cand × Option Cand) (c : Cand) :
    Option Cand × Option Cand :=
  match acc.1 with
  | none => (some c, acc.2)
  | some b =>
    if better c b then (some c, acc.1)
    else match acc.2 with
      | none => (acc.1, some c)
      | some b2 => if better c b2 then (acc.1, some c) else acc

/-- Insert one BG layer's hit (if enabled and non-transparent). -/
@[inline] def bgInsert (sp : BgSpan) (palT : Array UInt32) (vram : ByteArray) (x ch : Nat)
    (acc : Option Cand × Option Cand) : Option Cand × Option Cand :=
  match bgLinePixel sp palT vram x with
  | some c =>
    topTwoInsert acc { prio := sp.prio, ord := ch + 1,
                       layer := ch, color := c }
  | none => acc

/-- Insert an optional candidate (OBJ slot). -/
@[inline] def optInsert (acc : Option Cand × Option Cand) (o : Option Cand) :
    Option Cand × Option Cand :=
  match o with
  | some c => topTwoInsert acc c
  | none => acc

/-- Top two candidates by (priority, order) in one pass. -/
def topTwo (cs : List Cand) : Option Cand × Option Cand :=
  cs.foldl topTwoInsert (none, none)

/-- Alpha mix of two ARGB colors (8-bit math; ±1 LSB vs HW 5-bit).
    Channels are unrolled (no per-call closure) for the pixel loop. -/
@[inline] def mixARGB (c1 c2 : UInt32) (eva evb : Nat) : UInt32 :=
  let r := Nat.min 255
    ((((c1.toNat >>> 16) &&& 0xFF) * eva + ((c2.toNat >>> 16) &&& 0xFF) * evb) / 16)
  let g := Nat.min 255
    ((((c1.toNat >>> 8) &&& 0xFF) * eva + ((c2.toNat >>> 8) &&& 0xFF) * evb) / 16)
  let b := Nat.min 255
    (((c1.toNat &&& 0xFF) * eva + (c2.toNat &&& 0xFF) * evb) / 16)
  (0xFF000000 : UInt32) ||| (w32 r <<< 16) ||| (w32 g <<< 8) ||| w32 b

/-- One brightness channel (unrolled below; `up` = toward white). -/
@[inline] def fxChan (v : Nat) (up : Bool) (evy : Nat) : Nat :=
  if up then Nat.min 255 (v + (255 - v) * evy / 16)
  else v - v * evy / 16

/-- Brightness adjust of one ARGB color (channels unrolled, no closure). -/
@[inline] def fxAdjust (c : UInt32) (up : Bool) (evy : Nat) : UInt32 :=
  let r := fxChan ((c.toNat >>> 16) &&& 0xFF) up evy
  let g := fxChan ((c.toNat >>> 8) &&& 0xFF) up evy
  let b := fxChan (c.toNat &&& 0xFF) up evy
  (0xFF000000 : UInt32) ||| (w32 r <<< 16) ||| (w32 g <<< 8) ||| w32 b

/-- Per-line color-effect setup: everything `framePixel` needs from
    BLDCNT/BLDALPHA/BLDY that doesn't vary with `x` (hoisted out of the
    pixel loop — 240× fewer register parses; registers are frame-constant
    across a render). -/
structure BlendCfg where
  mode : Nat := 0
  eva : Nat := 16
  evb : Nat := 0
  evy : Nat := 0
  tgt1 : Nat := 0
  tgt2 : Nat := 0
deriving DecidableEq, Repr

def blendCfg (ppu : AgbPpu) : BlendCfg :=
  let bc := ppu.bldcnt.toNat
  { mode := (bc >>> 6) &&& 0x3
    eva := Nat.min 16 (ppu.bldalpha.toNat &&& 0x1F)
    evb := Nat.min 16 ((ppu.bldalpha.toNat >>> 8) &&& 0x1F)
    evy := Nat.min 16 (ppu.bldy.toNat &&& 0x1F)
    tgt1 := bc &&& 0x3F
    tgt2 := (bc >>> 8) &&& 0x3F }

/-- Full Mode-0 pixel with color effects (GBATEK "Color Special Effects").
    Target matching: top pixel must be a 1st target (semi OBJs always
    are), second-best a 2nd target; else the top pixel shows plain.
    Brightness applies when selected (semi falls back to it without an
    overlapping 2nd target). Window gating unmodeled: effects are global. -/
def framePixelCfg (bc : BlendCfg) (ppu : AgbPpu) (palT : Array UInt32)
    (vram : ByteArray) (sps : List AgbSprite) (spans : Array BgSpan)
    (y x : Nat) : UInt32 :=
  let back := palT.getD 0 0xFFFFFFFF
  let bd : Cand := { prio := 4, ord := 6, layer := 5, color := back }
  -- Same candidate SET as `bgHits ++ obj.toList ++ [bd]` (each layer
  -- hits at most once, so insertion order cannot change the top two).
  let acc := bgInsert (spans.getD 0 {}) palT vram x 0 (none, none)
  let acc := bgInsert (spans.getD 1 {}) palT vram x 1 acc
  let acc := bgInsert (spans.getD 2 {}) palT vram x 2 acc
  let acc := bgInsert (spans.getD 3 {}) palT vram x 3 acc
  let acc := optInsert acc (objHit ppu palT vram sps y x)
  let (top, second) := topTwoInsert acc bd
  match top with
  | none => back
  | some t =>
    let firstOK := t.semi || (((bc.tgt1 >>> t.layer) &&& 1) == 1)
    let secondOK : Bool :=
      match second with
      | some s => (((bc.tgt2 >>> s.layer) &&& 1) == 1)
      | none => false
    if (bc.mode == 1 || t.semi) && firstOK && secondOK then
      match second with
      | some s => mixARGB t.color s.color bc.eva bc.evb
      | none => t.color
    else if bc.mode == 2 || bc.mode == 3 then
      if (((bc.tgt1 >>> t.layer) &&& 1) == 1) then
        fxAdjust t.color (bc.mode == 2) bc.evy
      else t.color
    else t.color

/-- `framePixel` with on-the-fly blend setup (proof/test entry point;
    the hot loop calls `framePixelCfg` with a per-line `blendCfg`). -/
def framePixel (ppu : AgbPpu) (palT : Array UInt32) (vram : ByteArray)
    (sps : List AgbSprite) (spans : Array BgSpan) (y x : Nat) : UInt32 :=
  framePixelCfg (blendCfg ppu) ppu palT vram sps spans y x

/-- Pixel loop over one scanline with a pre-parsed sprite list,
    precomputed BG spans and blend setup. -/
def mode0LineLoopCfg (bc : BlendCfg) (ppu : AgbPpu) (palT : Array UInt32)
    (vram : ByteArray) (sps : List AgbSprite) (spans : Array BgSpan)
    (y : Nat) (fb : Array UInt32) : Nat → Array UInt32
  | 0 => fb
  | fuel + 1 =>
    let x := agbWidth - (fuel + 1)
    mode0LineLoopCfg bc ppu palT vram sps spans y
      (agbPlot fb x y (framePixelCfg bc ppu palT vram sps spans y x)) fuel

/-- Pixel loop over one scanline with a pre-parsed sprite list and
    precomputed BG spans. -/
def mode0LineLoop (ppu : AgbPpu) (palT : Array UInt32) (vram : ByteArray)
    (sps : List AgbSprite) (spans : Array BgSpan)
    (y : Nat) (fb : Array UInt32) : Nat → Array UInt32
  | 0 => fb
  | fuel + 1 =>
    let x := agbWidth - (fuel + 1)
    mode0LineLoop ppu palT vram sps spans y
      (agbPlot fb x y (framePixel ppu palT vram sps spans y x)) fuel

/-- Blit one mode-0 scanline (`fuel = agbWidth` covers x = 239..0).
    Sprites filtered from the per-frame parse table, BG layers set up
    and blend registers parsed once per line, not per pixel. -/
def mode0BlitLine (ppu : AgbPpu) (palT : Array UInt32) (vram : ByteArray)
    (parsed : Array (Option AgbSprite)) (y : Nat)
    (fb : Array UInt32) (fuel : Nat) : Array UInt32 :=
  mode0LineLoopCfg (blendCfg ppu) ppu palT vram (spritesOnLineParsed parsed y)
    #[bgSpan ppu 0 y, bgSpan ppu 1 y, bgSpan ppu 2 y, bgSpan ppu 3 y] y fb fuel

/-- Render `lines` mode-0 scanlines (top-down) over the framebuffer
    (palette + OAM table precomputed once per render). -/
def renderMode0 (ppu : AgbPpu) (pal vram oam : ByteArray) (fb : Array UInt32)
    (lines : Nat) : Array UInt32 :=
  let palT := palARGB pal
  let parsed := parseOam oam
  (List.range lines).foldl
    (fun fb k => mode0BlitLine ppu palT vram parsed k fb agbWidth) fb

end AGB
