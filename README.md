# lean-gameboy

A Nintendo Game Boy (DMG) emulator written in Lean 4 — pure functional
hardware model plus a native SDL2 frontend. Built with
[`elan`](https://github.com/leanprover/elan) +
[Lake](https://github.com/leanprover/lean4/tree/master/src/lake);
pinned to `leanprover/lean4:v4.34.0` (see `lean-toolchain`).

## Status

Full DMG system: LR35902 CPU (all 512 opcodes incl. `DAA`/HALT bug),
memory map, MBC1/MBC3/MBC5 (+NoMBC), timer, interrupts, tile-mode PPU
(BG/window/sprites, all STAT modes), joypad, serial stub (Blargg
protocol), and a 4-channel APU with 512 Hz sequencer. Boots straight
into the cartridge (boot ROM skipped, DMG defaults applied).

**Tetris (U) 1.1 verified playable**: logo → copyright → title →
menu → gameplay with falling/moving pieces, score/level/lines panels
and NEXT preview (screenshots via `--dump`). Scripted run:
`--input "start@950+10,start@1400+10,start@2500+10"`.

**Game Boy Color**: CGB cartridges boot into color mode (flag `0x143`,
`A=$11` boot regs): 8×4 KiB WRAM banks (`SVBK`), 2×8 KiB VRAM banks
(`VBK`), 8+8 15-bit palettes with auto-increment (`BGPI/BGPD`,
`OBPI/OBPD`), tile-map attributes (palette/bank/flips/priority),
color scanline renderer with CGB sprite priority, GDMA + HBlank DMA
(`HDMA1-5`), and double-speed mode (`KEY1` + `STOP`, 2 T-cycles per
M-cycle through timer/serial/APU/PPU).

**Pokémon Crystal (U) 1.1 verified booting**: copyright → Game Freak
logo → intro sequence in full color (60 s headless run reaches the
animated intro with 18 on-screen colors; long black transitions in
between are the game's own scene fades). `gb-test` pins the CGB
hardware: WRAM/VRAM bank isolation, palette auto-increment +
readback, `KEY1`/`STOP` speed switch with ~35k-cycle double-speed
frames, GDMA bytes + cost, HBlank-DMA completion, white CGB frame.

**Blargg `cpu_instrs` conformance**: all 11 individual ROMs `Passed`
plus the bank-switched composite `Passed all tests` (MBC1, timer,
interrupts, memory timing paths covered). Run test ROMs by cycles
(LCD-off ROMs never produce frame boundaries):
`lean-gameboy 11.gb --headless --cycles 200000000`.

**Halt-bug proofs** (`Proofs/Halt.lean`): double-halt spin (PC frozen,
bug re-armed), single fall-through arming, bugged-immediate shift,
and `len - 1` advance — the exact mechanism `double-halt-cancel`
validates empirically.

**Sprite priority fix + proofs** (`Proofs/Sprite.lean`): OAM bit 7 was
negated, burying every `attr = 0` sprite behind nonzero background
(invisible Tetris menu cursors — the arrow/title sprite survived only
over color-0). Attribute decoding is now pinned per-bit.

**`double-halt-cancel` (nitro2k01): PASS** — correct double-`HALT`
spin with IME=0, inhibited return address (`RST $38` pushes the
un-incremented PC), VRAM-inaccessible code fetch reading `$FF`,
and matching DIV timing. This required the full halt-bug model:
fall-through arms the bug without advancing, bugged immediates shift
down one byte, and a bugged `HALT` re-arms instead of advancing.

**Machine-checked proofs** (`LeanGameboy/Proofs/`, all kernel-checked
at build time, zero `sorry`/`axiom`): ALU flag contracts, identity,
commutativity and `Nat`-level characterization (`Arith`), exact AF
codec bit positions (`Regs`), full invalid-opcode set + exhaustive
length/coverage over all 512 opcodes (`Decode`), 12 memory-map
non-interference lemmas + exact cycle accounting + HDMA/scanline
cycle preservation (`Bus`), timer edge
cases + IRQ acknowledgement (`Timer`), PPU modes, palette bounds,
interrupt priority (`Ppu`), APU phase-step frame preservation (`Apu`),
halt-bug spin/arming/immediates (`Halt`),
sprite attribute decoding (`Sprite`). Bounded reachability: a 132k-instruction
scripted run is proven to reach its target state via `native_decide`
(`Reach` — kernel `decide` cannot scale there; full-game traces are
provably out of reach, see that file). Open goals for later:
per-instruction cycle lower bounds (60-arm automation) and channel
phase-additivity (div/mod composition).

Verified where it counts: the kernel-checked proof suite above
plus a headless end-to-end suite
(`gb-test`: ALU/`DAA` results, JR loop, frame advance, VBlank IRQ,
cycle counts, timer edge/overflow behavior).

## Build

```sh
elan default leanprover/lean4:v4.34.0
lake build
```

No SDL dev packages needed: `c/shim.c` loads `libSDL2` with `dlopen`
at runtime (links only `-ldl`). Without SDL2 present, the executable
still builds and runs headless.

## Run

```sh
# windowed (arrows = d-pad, X = A, Z = B, Enter = Start, RShift = Select,
# F1 = dump snapN.ppm + snapN.txt hardware snapshot for debugging)
./.lake/build/bin/lean-gameboy game.gb --scale 3

# headless (CI / Blargg): run N frames, dump framebuffer + serial log
./.lake/build/bin/lean-gameboy game.gb --headless --frames 600 --dump frame.ppm

# scripted input for headless playtests: btn@startFrame+holdFrames,...
./.lake/build/bin/lean-gameboy game.gb --headless --frames 4200 \
  --input "start@950+10,left@3600+30,a@3900+5" --dump frame.ppm

# debug a soft-lock: registers, IRQ/PPU/timer state, PC samples, trace
./.lake/build/bin/lean-gameboy game.gb --headless --frames 3400 --debug

# self-test (synthetic ROM, no game needed)
lake build gb-test && ./.lake/build/bin/gb-test
```

Battery saves load/store automatically as `<rom>.sav`.

## Layout

- `LeanGameboy/Basic.lean` — bit/byte helpers
- `LeanGameboy/Cgb.lean` — CGB banking/palette/HDMA helpers, BGR555 output
- `LeanGameboy/Cpu/{Regs,Decode}.lean` — registers/flags, 512-opcode tables
- `LeanGameboy/Cartridge/{Header,Mbc}.lean` — header parse, banking
- `LeanGameboy/{Timer,Interrupts,Joypad,Serial}.lean` — peripherals
- `LeanGameboy/{Ppu,Framebuffer}.lean` — scanline renderer, RGB output
- `LeanGameboy/Apu.lean` — square/wave/noise + mixer (~44.1 kHz)
- `LeanGameboy/Bus.lean` — memory map, CPU executor, IRQ dispatch
- `LeanGameboy/Emu.lean` — frame stepping, PPM dumps, `.sav`
- `LeanGameboy/Sdl/{Ffi,Driver}.lean` + `c/shim.c` — SDL frontend
- `LeanGameboy/Proofs/{Arith,Regs,Decode,Bus,Timer,Ppu,Apu,Halt,Sprite,Reach}.lean`
  — machine-checked proof suite (see below)
- `Tests/Smoke.lean` (`gb-test`) — end-to-end smoke suite
- `Main.lean` — CLI

## Design notes

- All hardware is **pure**: `GBState → GBState`. Only `Main`/SDL do `IO`.
- Cycle model: M-cycles in the CPU, dots elsewhere; APU channels advance
  in bulk (O(1) phase math); the timer counts divider falling edges
  exactly with integer division.
- Known v1 deviations: fixed 172-dot Mode 3 (no per-sprite penalty),
  OAM-order sprite priority, MBC2/MMM01/HuC/MBC6/7 read flat, `STOP`
  behaves like `HALT` in DMG mode, invalid opcodes NOP instead of
  locking up, MBC3 RTC reads as `0xFF` (Crystal boots/plays; clock
  events frozen), no speed-switch stall cycles (~2 ms switch is
  instant), `FF6C`/`FF72-77` unmapped, CGB OBJ priority is pure OAM
  order (no X-coordinate tiebreak).
- Performance: ~14 ms/frame headless with sound, +~1.5 ms for the
  SDL present path (direct `Array UInt32` upload, no byte conversion)
  — real-time with margin. Hot-path techniques: lazy APU phase-debt
  (timers advance arithmetically; phases flush only at sample points
  and register writes), unboxed `ByteArray` sample buffer (boxed
  `Array Int` made GC marking scale with buffer size), O(1) channel
  phase math, exact divider-edge timer counting, allocation-free
  scanline loops.
  See `Tests/Bench.lean` (`gb-bench`) for the subsystem breakdown.
