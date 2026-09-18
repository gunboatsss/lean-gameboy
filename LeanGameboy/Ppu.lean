/-
  LeanGameboy.Ppu — DMG picture processing unit (tile mode).

  Timing: 456 dots/scanline, 154 scanlines (144 visible + 10 VBlank).
  Modes: 2 = OAM scan (0..80), 3 = draw (80..252), 0 = HBlank,
  1 = VBlank. Mode-3 length is fixed at 172 dots in v1 (no per-sprite
  penalty); the FIFO is modelled as a scanline renderer in
  `renderLine`.
-/
import LeanGameboy.Basic
import LeanGameboy.Cgb

namespace GB

/-- PPU registers + mode bookkeeping. -/
structure PpuState where
  lcdc : UInt8 := 0x91
  stat : UInt8 := 0
  scy : UInt8 := 0
  scx : UInt8 := 0
  ly : UInt8 := 0
  lyc : UInt8 := 0
  wy : UInt8 := 0
  wx : UInt8 := 0
  bgp : UInt8 := 0xFC
  obp0 : UInt8 := 0xFF
  obp1 : UInt8 := 0xFF
  dots : Nat := 0        -- dots elapsed in the current scanline
  mode : Nat := 0        -- cached STAT mode bits
  statLine : Bool := false  -- current STAT interrupt line level
  vblankIrq : Bool := false -- VBlank interrupt requested (edge)
  frame : Nat := 0
deriving DecidableEq, Repr

namespace PpuState

/-- STAT mode for the current position. -/
def curMode (p : PpuState) : Nat :=
  if p.ly.toNat >= 144 then 1
  else if p.dots < 80 then 2
  else if p.dots < 252 then 3
  else 0

/-- STAT interrupt line level (LYC + mode enables). -/
def statLevel (p : PpuState) (mode : Nat) : Bool :=
  let lycEq := p.ly == p.lyc
  (bitGet p.stat 6 && lycEq) ||
  (bitGet p.stat 5 && mode == 2) ||
  (bitGet p.stat 4 && mode == 1) ||
  (bitGet p.stat 3 && mode == 0)

/-- Advance the PPU by `dots` T-cycles.
    Returns the updated state plus flags:
    `(vblankEdge, statRising, lineDone, frameDone)`. -/
def step (p : PpuState) (dots : Nat) : PpuState × Bool × Bool × Bool × Bool :=
  if dots == 0 then (p, false, false, false, false)
  else
    let lcdOn := bitGet p.lcdc 7
    if !lcdOn then
      -- LCD off: LY/DOTS frozen at 0, STAT cleared.
      ({ p with
        ly := 0
        dots := 0
        mode := 0
        stat := bitClear (bitClear p.stat 1) 0 }, false, false, false, false)
    else
      let total := p.dots + dots
      let adv := total / 456
      let dots' := total % 456
      -- advance LY over however many scanlines elapsed
      let rec advLy : Nat → Nat → Nat × Bool
        | 0, ly => (ly, false)
        | k + 1, ly =>
          let ly' := (ly + 1) % 154
          let (rest, wrapped) := advLy k ly'
          (rest, wrapped || ly' == 0)
      let (lyN, wrapped) := advLy adv p.ly.toNat
      let p1 := { p with dots := dots', ly := w8 lyN }
      let mode := p1.curMode
      -- VBlank entry edge: LY crossed from <144 to >=144
      let enteredVblank : Bool :=
        p.ly.toNat < 144 && lyN >= 144
      let lineDone : Bool := dots' < p.dots || adv > 0
      let lvl := p1.statLevel mode
      let statRising := lvl && !p.statLine
      let stat := ((p.stat &&& 0xF8) ||| w8 mode) |||
        (if p1.ly == p1.lyc then 0x04 else 0x00)
      let p2 := { p1 with
        mode := mode
        stat := stat
        statLine := lvl
        vblankIrq := p.vblankIrq || enteredVblank
        frame := p.frame + (if wrapped && lyN == 0 then 1 else 0) }
      (p2, enteredVblank, statRising, lineDone, wrapped && lyN == 0)

/-- Acknowledge the VBlank interrupt. -/
def ackVblank (p : PpuState) : PpuState :=
  { p with vblankIrq := false }

-- ------------------------------------------------------------------
-- Scanline renderer (called once per visible scanline at HBlank).
-- Produces 160 palette indices (0..3) plus per-pixel OBJ priority info.
-- ------------------------------------------------------------------

/-- One decoded background/window pixel: colour index + tile priority. -/
structure BgPix where
  color : Nat
  prio : Bool   -- BG-to-OBJ priority bit of the tile attributes (always false on DMG)
deriving DecidableEq, Repr

/-- Fetch a single tile pixel (0..7, MSB first) without allocation. -/
def tilePix (vram : ByteArray) (base : Nat) (i : Nat) : Nat :=
  let lo := bget vram base
  let hi := bget vram (base + 1)
  let b := 7 - (i % 8)
  (if bitGet hi b then 2 else 0) + (if bitGet lo b then 1 else 0)

/-- Tile data address for a tile id (signed or unsigned addressing). -/
def tileAddr (signed : Bool) (id : UInt8) : Nat :=
  if signed then
    let s : Int := id.toNat - (if id.toNat >= 128 then 256 else 0)
    (0x1000 + s * 16).toNat
  else id.toNat * 16

/-- Map a 2-bit index through a DMG palette register. -/
def palMap (pal : UInt8) (idx : Nat) : Nat :=
  ((pal.toNat >>> (2 * (idx % 4))) % 4)

/-- Render background+window scanline → 160 palette-mapped shades.
    Allocation-free pixel loop (no intermediate lists). -/
def renderBg (p : PpuState) (vram : ByteArray) : Array Nat :=
  let bgOn := bitGet p.lcdc 0
  let winOn := bitGet p.lcdc 5 && p.wy.toNat <= p.ly.toNat
  let signed := !bitGet p.lcdc 4
  let bgMap := if bitGet p.lcdc 3 then 0x1C00 else 0x1800
  let winMap := if bitGet p.lcdc 6 then 0x1C00 else 0x1800
  let pix (x : Nat) : Nat :=
    let (mapBase, px, py) :=
      if winOn && x + 7 >= p.wx.toNat then
        (winMap, x + 7 - p.wx.toNat, p.ly.toNat - p.wy.toNat)
      else
        (bgMap, (x + p.scx.toNat) % 256, (p.ly.toNat + p.scy.toNat) % 256)
    if !bgOn then 0
    else
      let tileId := bget vram (mapBase + (py / 8) * 32 + (px / 8))
      palMap p.bgp (tilePix vram (tileAddr signed tileId + (py % 8) * 2) (px % 8))
  let rec loop (x : Nat) (acc : Array Nat) : Array Nat :=
    if x >= 160 then acc else loop (x + 1) (acc.push (pix x))
  loop 0 (Array.mkEmpty 160)

/-- One OAM sprite entry. -/
structure Sprite where
  y : Nat
  x : Nat
  tile : Nat
  prio : Bool
  yFlip : Bool
  xFlip : Bool
  pal : Bool  -- false = OBP0, true = OBP1
  cgbPal : Nat := 0  -- CGB OBJ palette 0..7 (attr bits 0-2)
  vbank : Nat := 0   -- CGB tile VRAM bank (attr bit 3)
deriving Repr, Inhabited

/-- Parse OAM entry `i` (0-39) into a `Sprite`. -/
def parseSprite (oam : ByteArray) (i : Nat) : Sprite :=
  let base := i * 4
  let attr := bget oam (base + 3)
  { y := (bget oam base).toNat, x := (bget oam (base + 1)).toNat,
    tile := (bget oam (base + 2)).toNat,
    -- OAM bit 7 set = BG/Window colors 1-3 over OBJ (sprite behind)
    prio := bitGet attr 7, yFlip := bitGet attr 6,
    xFlip := bitGet attr 5, pal := bitGet attr 4,
    cgbPal := attr.toNat % 8, vbank := (attr.toNat / 8) % 2 }

/-- Parse all 40 OAM entries. -/
def parseOam (oam : ByteArray) : Array Sprite :=
  Array.mk (List.range 40 |>.map (parseSprite oam))

/-- Apply OBJ layer over a background line.
    Returns final shade indices (palettes already applied). -/
def renderLine (p : PpuState) (vram oam : ByteArray) : Array Nat :=
  let bg := renderBg p vram
  let tall := bitGet p.lcdc 2
  let h : Nat := if tall then 16 else 8
  let objOn := bitGet p.lcdc 1
  if !objOn then bg
  else
    -- cheap pre-scan: skip all sprite work if no sprite Y overlaps this line
    let ly16 := p.ly.toNat + 16
    let rec hasHit (i : Nat) : Bool :=
      if i >= 40 then false
      else
        let y := (bget oam (i * 4)).toNat
        if ly16 >= y && ly16 < y + h then true else hasHit (i + 1)
    if !hasHit 0 then bg
    else
      let sps := parseOam oam
      -- up to 10 sprites per line, OAM order = priority (v1);
      -- collected as an array to avoid quadratic `(++)` appends
      let hits : Array Nat :=
        (List.range 40).foldl (fun (acc : Array Nat) i =>
          if acc.size >= 10 then acc
          else
            let s := sps[i]!
            if p.ly.toNat + 16 >= s.y && p.ly.toNat + 16 < s.y + h then acc.push i
            else acc) #[]
      if hits.size == 0 then bg
      else
        let rec loop (x : Nat) (line : Array Nat) : Array Nat :=
          if x >= 160 then line
          else
            let pick := hits.foldl (fun (best : Option (Nat × Nat × Nat)) i =>
              let s := sps[i]!
              if x + 8 >= s.x && x + 8 < s.x + 8 then
                let sx := if s.xFlip then 7 - (x + 8 - s.x) else (x + 8 - s.x)
                let sy0 := p.ly.toNat + 16 - s.y
                let sy := if s.yFlip then (h - 1 - sy0) else sy0
                let tile := if tall then (s.tile &&& 0xFE) + (sy / 8) else s.tile
                let c := tilePix vram (tile * 16 + (sy % 8) * 2) sx
                if c == 0 then best
                else
                  let shade := palMap (if s.pal then p.obp1 else p.obp0) c
                  match best with
                  | none => some (i, s.x, shade)
                  | some (_, bx, _) => if s.x < bx then some (i, s.x, shade) else best
              else best) none
            let line :=
              match pick with
              | none => line
              | some (i, _, c) =>
                let s := sps[i]!
                let bgc := line[x]!
                -- OBJ-to-BG priority: if set and bg shade != 0, bg wins
                if s.prio && bgc != 0 then line else line.set! x c
            loop (x + 1) line
        loop 0 bg

-- ------------------------------------------------------------------
-- CGB color renderer. Tile maps live in VRAM bank 0, per-tile
-- attributes (palette, bank, flips, priority) at the same offsets in
-- bank 1. Colors come from palette RAM (`bgPal`/`obPal`: 8×4 BGR555).
-- ------------------------------------------------------------------

/-- CGB background map attribute (VRAM bank 1). -/
structure CgbBgAttr where
  pal : Nat
  bank : Nat
  xFlip : Bool
  yFlip : Bool
  prio : Bool
deriving DecidableEq, Repr

/-- Decode a CGB map attribute byte. -/
def parseBgAttr (v : UInt8) : CgbBgAttr :=
  { pal := v.toNat % 8, bank := (v.toNat / 8) % 2,
    xFlip := bitGet v 5, yFlip := bitGet v 6, prio := bitGet v 7 }

/-- Look up a BGR555 palette color. -/
def palColor (pal : Array UInt16) (i : Nat) : UInt16 :=
  if h : i < pal.size then pal[i]'h else 0x7FFF

/-- Render background+window scanline → per-pixel (ARGB, color idx, prio). -/
def renderBgCgb (p : PpuState) (vram : ByteArray) (bgPal : Array UInt16) :
    Array (UInt32 × Nat × Bool) :=
  let winOn := bitGet p.lcdc 5 && p.wy.toNat <= p.ly.toNat
  let signed := !bitGet p.lcdc 4
  let bgMap := if bitGet p.lcdc 3 then 0x1C00 else 0x1800
  let winMap := if bitGet p.lcdc 6 then 0x1C00 else 0x1800
  -- LCDC.0 clear disables BG+window layer entirely (white behind sprites)
  if !bitGet p.lcdc 0 then
    Array.mk (List.replicate 160 (0xFFFFFFFF, 0, false))
  else
    let pix (x : Nat) : UInt32 × Nat × Bool :=
      let (mapBase, px, py) :=
        if winOn && x + 7 >= p.wx.toNat then
          (winMap, x + 7 - p.wx.toNat, p.ly.toNat - p.wy.toNat)
        else
          (bgMap, (x + p.scx.toNat) % 256, (p.ly.toNat + p.scy.toNat) % 256)
      let off := (py / 8) * 32 + (px / 8)
      let tileId := bget vram (mapBase + off)
      let attr := parseBgAttr (bget vram (0x2000 + mapBase + off))
      let tx := if attr.xFlip then 7 - (px % 8) else (px % 8)
      let ty := if attr.yFlip then 7 - (py % 8) else (py % 8)
      let base := attr.bank * 0x2000 + tileAddr signed tileId + ty * 2
      let idx := tilePix vram base tx
      (cgbColor (palColor bgPal (attr.pal * 4 + idx)), idx, attr.prio)
    let rec loop (x : Nat) (acc : Array (UInt32 × Nat × Bool)) : Array (UInt32 × Nat × Bool) :=
      if x >= 160 then acc else loop (x + 1) (acc.push (pix x))
    loop 0 (Array.mkEmpty 160)

/-- CGB sprite-vs-BG mix decision: `true` = BG pixel wins.
    Pan Docs "BG-to-OBJ Priority in CGB Mode" truth table: BG color 0
    → OBJ; master (LCDC.0) clear → OBJ; both priority bits clear →
    OBJ; otherwise (BG opaque, master set, *either* bit set) → BG. -/
def cgbMixBgWins (bgIdx : Nat) (master spritePrio bgPrio : Bool) : Bool :=
  bgIdx != 0 && master && (spritePrio || bgPrio)

/-- Apply OBJ layer over a CGB background line → final ARGB colors.
    In particular an OAM bit-7-set sprite goes behind *any* opaque BG
    pixel (tile bit is not required), and a tile-priority BG pixel
    covers even a priority-clear sprite (e.g. the Crystal title logo
    over the crystal). -/
def renderLineCgb (p : PpuState) (vram oam : ByteArray)
    (bgPal obPal : Array UInt16) : Array UInt32 :=
  let bg := renderBgCgb p vram bgPal
  let tall := bitGet p.lcdc 2
  let h : Nat := if tall then 16 else 8
  let objOn := bitGet p.lcdc 1
  let master := bitGet p.lcdc 0
  if !objOn then bg.map (fun t => t.1)
  else
    let ly16 := p.ly.toNat + 16
    let rec hasHit (i : Nat) : Bool :=
      if i >= 40 then false
      else
        let y := (bget oam (i * 4)).toNat
        if ly16 >= y && ly16 < y + h then true else hasHit (i + 1)
    if !hasHit 0 then bg.map (fun t => t.1)
    else
      let sps := parseOam oam
      let hits : Array Nat :=
        (List.range 40).foldl (fun (acc : Array Nat) i =>
          if acc.size >= 10 then acc
          else
            let s := sps[i]!
            if p.ly.toNat + 16 >= s.y && p.ly.toNat + 16 < s.y + h then acc.push i
            else acc) #[]
      if hits.size == 0 then bg.map (fun t => t.1)
      else
        -- CGB priority is OAM order: first opaque sprite pixel wins
        let pick (x : Nat) : Option (Sprite × UInt32) :=
          hits.foldl (fun (best : Option (Sprite × UInt32)) i =>
            match best with
            | some _ => best
            | none =>
              let s := sps[i]!
              if x + 8 >= s.x && x + 8 < s.x + 8 then
                let sx := if s.xFlip then 7 - (x + 8 - s.x) else (x + 8 - s.x)
                let sy0 := p.ly.toNat + 16 - s.y
                let sy := if s.yFlip then (h - 1 - sy0) else sy0
                let tile := if tall then (s.tile &&& 0xFE) + (sy / 8) else s.tile
                let c := tilePix vram (s.vbank * 0x2000 + tile * 16 + (sy % 8) * 2) sx
                if c == 0 then none
                else some (s, cgbColor (palColor obPal (s.cgbPal * 4 + c)))
              else none) none
        let rec loop (x : Nat) (line : Array UInt32) : Array UInt32 :=
          if x >= 160 then line
          else
            let (bgc, bgIdx, bgPrio) := bg[x]!
            let out :=
              match pick x with
              | none => bgc
              | some (s, c) =>
                if cgbMixBgWins bgIdx master s.prio bgPrio then bgc else c
            loop (x + 1) (line.set! x out)
        loop 0 (bg.map (fun t => t.1))

end PpuState

end GB
