/-
  LeanAGB.Emu — headless driver: instruction batches, frame stepping
  (280896 cycles), ROM loading. Mirrors LeanGameboy.Emu shape.
-/
import LeanAGB.Bus

namespace AGB

def loadROM (bytes : ByteArray) : AGBState :=
  AGBState.fresh bytes

/-- Encode the backup media for `<rom>.sav`. -/
def saveGame (s : AGBState) : ByteArray := saveEncode s.save

/-- Restore backup media (empty file = keep fresh state). -/
def loadGame (s : AGBState) (bytes : ByteArray) : AGBState :=
  if bytes.size == 0 then s else { s with save := saveDecode bytes }

def runInstrs : AGBState → Nat → AGBState
  | s, 0 => s
  | s, k + 1 => runInstrs (stepCPU s) k

/-- Run until one full frame elapses (cycle-count based; PPU has no pixels yet).
    Halted stretches fast-forward via `stepHaltJump` (exact: no wake
    event can land strictly inside a jump). -/
def runFrame (s : AGBState) : AGBState :=
  let target := s.cycles + AGB_CYCLES_PER_FRAME
  let rec loop : AGBState → Nat → AGBState
    | st, 0 => st
    | st, k + 1 =>
      if st.cycles >= target then st
      else loop (if st.halted then stepHaltJump st else stepCPU st) k
  loop s (AGB_CYCLES_PER_FRAME + 1000)

def runFrames : AGBState → Nat → AGBState
  | s, 0 => s
  | s, k + 1 => runFrames (runFrame s) k

/-- Run until `cycles` more cycles elapse (test-ROM path; halt-aware). -/
def runUntilCycles (s : AGBState) (cycles : Nat) : AGBState :=
  let target := s.cycles + cycles
  let rec loop : AGBState → Nat → AGBState
    | st, 0 => st
    | st, k + 1 =>
      if target <= st.cycles then st
      else loop (if st.halted then stepHaltJump st else stepCPU st) k
  loop s (cycles + 1000)

/-- White fill (forced blank: DISPCNT.7 shows white regardless of
    mode or layers; GBATEK LCD control). -/
def renderBlank (fb : Array UInt32) : Array UInt32 :=
  (List.range (agbWidth * agbHeight)).foldl
    (fun fb i => agbPlot fb (i % agbWidth) (i / agbWidth) 0xFFFFFFFF) fb

/-- Refresh `fb` from video memory for the selected DISPCNT mode
    (0 = text BGs, 3/4/5 = bitmaps; 1/2 keep `fb`, open gap). -/
def renderFrame (s : AGBState) : AGBState :=
  if ((s.ppu.dispcnt.toNat >>> 7) &&& 1) == 1 then
    { s with fb := renderBlank s.fb }
  else if (s.ppu.dispcnt.toNat &&& 7) == 0 then
    { s with fb := renderMode0 s.ppu s.pal s.vram s.oam s.fb agbHeight }
  else if (s.ppu.dispcnt.toNat &&& 7) == 3 then
    { s with fb := renderMode3 s.vram s.fb agbHeight }
  else if (s.ppu.dispcnt.toNat &&& 7) == 4 then
    let page := (s.ppu.dispcnt.toNat >>> 4) &&& 1
    { s with fb := renderMode4 s.pal s.vram page s.fb agbHeight }
  else if (s.ppu.dispcnt.toNat &&& 7) == 5 then
    let page := (s.ppu.dispcnt.toNat >>> 4) &&& 1
    { s with fb := renderMode5 s.pal s.vram page s.fb }
  else s

/-- Exact render memo: `renderFrame` output depends only on the
    `RenderView` + pal/vram/oam bytes, so a key match reuses the cached
    framebuffer bit-for-bit (exact: `ByteArray` equality is byte-wise;
    snapshots share until the emulator's next write, and a hit returns
    the very array a fresh render would have produced — see
    `memoRenderFrame_hit`). Modes 1/2 keep `fb`, but their render path
    is already a no-op, so the memo never costs them anything. -/
structure RenderMemo where
  view : RenderView := {}
  pal : ByteArray := ByteArray.empty
  vram : ByteArray := ByteArray.empty
  oam : ByteArray := ByteArray.empty
  fb : Array UInt32 := #[]
  valid : Bool := false

/-- Refresh `fb` through the memo: full key match reuses the cached
    framebuffer, otherwise renders and re-snapshots. Byte compares
    short-circuit on the first differing byte, so animated frames pay
    ~one memcmp per region and static frames skip the ~18 ms render. -/
def memoRenderFrame (s : AGBState) (m : RenderMemo) : AGBState × RenderMemo :=
  let v := renderView s.ppu
  if m.valid && m.view == v && m.pal == s.pal && m.vram == s.vram
      && m.oam == s.oam then
    ({ s with fb := m.fb }, m)
  else
    let s := renderFrame s
    let m : RenderMemo :=
      { view := v, pal := s.pal, vram := s.vram, oam := s.oam, fb := s.fb,
        valid := true }
    (s, m)

/-- Dump framebuffer as binary P6 PPM (240×160). -/
def dumpPPM (s : AGBState) (path : System.FilePath) : IO Unit := do
  let s := renderFrame s
  let header : Array UInt8 :=
    "P6\n240 160\n255\n".toList.toArray.map (fun c => w8 c.toNat)
  let px (c : UInt32) : Array UInt8 :=
    #[w8 ((c >>> 16).toNat % 256), w8 ((c >>> 8).toNat % 256), w8 (c.toNat % 256)]
  let body := (List.range (agbWidth * agbHeight)).foldl
    (fun acc i => acc ++ px (s.fb.getD i 0xFFFFFFFF)) #[]
  IO.FS.writeBinFile path (ByteArray.mk (header ++ body))

/-- Little-endian u16 push for debug snapshots. -/
def pushU16LE (b : ByteArray) (v : UInt16) : ByteArray :=
  b ++ ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8]

/-- Little-endian u32 push for debug snapshots. -/
def pushU32LE (b : ByteArray) (v : UInt32) : ByteArray :=
  b
    ++ ByteArray.mk
      #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8,
        (v >>> 24).toUInt8]

/-- Debug render-state snapshot: every input `renderFrame` reads
    (view regs + pal/vram/oam), so a broken scene can be reproduced
    headlessly bit-for-bit. Written next to F1 PPM snapshots. -/
def dumpRenderState (s : AGBState) : ByteArray :=
  let magic := ByteArray.mk (Array.mk ("AGBRS01".toList.map (fun c => w8 c.toNat)))
  let regs := #[s.ppu.dispcnt, s.ppu.bldcnt, s.ppu.bldalpha, s.ppu.bldy]
  let b := regs.foldl pushU16LE magic
  let b := (s.ppu.bgcnt ++ s.ppu.bghofs ++ s.ppu.bgvofs).foldl pushU16LE b
  let b := pushU32LE (pushU32LE (pushU32LE b s.pal.size.toUInt32)
    s.vram.size.toUInt32) s.oam.size.toUInt32
  b ++ s.pal ++ s.vram ++ s.oam

/-- Parse `dumpRenderState` output (none = bad magic/size). -/
def parseRenderState (b : ByteArray) :
    Option (AgbPpu × ByteArray × ByteArray × ByteArray) :=
  let magic := ByteArray.mk (Array.mk ("AGBRS01".toList.map (fun c => w8 c.toNat)))
  if b.size < 7 + 32 + 12 then none
  else if b.extract 0 7 != magic then none
  else
    let u16 (i : Nat) : UInt16 := bget16LE b (7 + i * 2)
    let ppu : AgbPpu :=
      { dispcnt := u16 0, bldcnt := u16 1, bldalpha := u16 2, bldy := u16 3,
        bgcnt := Array.mk ((List.range 4).map (fun i => u16 (4 + i))),
        bghofs := Array.mk ((List.range 4).map (fun i => u16 (8 + i))),
        bgvofs := Array.mk ((List.range 4).map (fun i => u16 (12 + i))) }
    let ps := (bget32LE b 39).toNat
    let vs := (bget32LE b 43).toNat
    let os := (bget32LE b 47).toNat
    if b.size != 51 + ps + vs + os then none
    else
      some
        (ppu, b.extract 51 (51 + ps), b.extract (51 + ps) (51 + ps + vs),
          b.extract (51 + ps + vs) (51 + ps + vs + os))

end AGB
