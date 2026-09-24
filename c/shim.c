/* lean-gameboy SDL shim.
 *
 * SDL2 is loaded at *runtime* with dlopen(), so building the emulator
 * never requires SDL headers or -lSDL2. If libSDL2 cannot be loaded,
 * every gb_* entry point degrades gracefully (window open reports
 * failure; blit/present/audio become no-ops; poll returns no input)
 * and Main falls back to headless mode.
 */
#include <dlfcn.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

#define FB_W 160
#define FB_H 144

/* forward: defined below, reused by agb_close */
lean_obj_res gb_close(lean_obj_arg w);

/* ---------------- dynamic SDL binding ---------------- */

static void *sdl_handle = NULL;
static int sdl_ok = 0;

static int (*p_Init)(uint32_t) = NULL;
static void (*p_Quit)(void) = NULL;
static const char *(*p_GetError)(void) = NULL;
static void *(*p_CreateWindow)(const char *, int, int, int, int, uint32_t) = NULL;
static void (*p_DestroyWindow)(void *) = NULL;
static void *(*p_CreateRenderer)(void *, int, uint32_t) = NULL;
static void (*p_DestroyRenderer)(void *) = NULL;
static void *(*p_CreateTexture)(void *, uint32_t, int, int, int) = NULL;
static int (*p_UpdateTexture)(void *, const void *, const void *, int) = NULL;
static void (*p_DestroyTexture)(void *) = NULL;
static int (*p_RenderClear)(void *) = NULL;
static int (*p_RenderCopy)(void *, void *, const void *, const void *) = NULL;
static void (*p_RenderPresent)(void *) = NULL;
static int (*p_PollEvent)(void *) = NULL;
static const uint8_t *(*p_GetKeyboardState)(int *) = NULL;
static uint32_t (*p_OpenAudioDevice)(const char *, int, const void *, void *, int) = NULL;
static void (*p_CloseAudioDevice)(uint32_t) = NULL;
static int (*p_QueueAudio)(uint32_t, const void *, uint32_t) = NULL;
static void (*p_PauseAudioDevice)(uint32_t, int) = NULL;
static uint32_t (*p_GetQueuedAudioSize)(uint32_t) = NULL;
static void (*p_Delay)(uint32_t) = NULL;
static uint64_t (*p_GetTicks64)(void) = NULL;

#define LOAD(sym)                                      \
    do {                                               \
        p_##sym = (void *)dlsym(sdl_handle, "SDL_" #sym); \
        if (!p_##sym) { sdl_ok = 0; return; }          \
    } while (0)

static void sdl_load(void) {
    static int tried = 0;
    if (tried) return;
    tried = 1;
    const char *names[] = {
        "libSDL2-2.0.so.0", "libSDL2.so",
        "libSDL2.dylib", "SDL2.dll", "SDL2-2.0.0.dll", NULL
    };
    for (int i = 0; names[i]; i++) {
        sdl_handle = dlopen(names[i], RTLD_NOW | RTLD_LOCAL);
        if (sdl_handle) break;
    }
    if (!sdl_handle) return;
    sdl_ok = 1;
    LOAD(Init);
    LOAD(Quit);
    LOAD(GetError);
    LOAD(CreateWindow);
    LOAD(DestroyWindow);
    LOAD(CreateRenderer);
    LOAD(DestroyRenderer);
    LOAD(CreateTexture);
    LOAD(UpdateTexture);
    LOAD(DestroyTexture);
    LOAD(RenderClear);
    LOAD(RenderCopy);
    LOAD(RenderPresent);
    LOAD(PollEvent);
    LOAD(GetKeyboardState);
    LOAD(OpenAudioDevice);
    LOAD(CloseAudioDevice);
    LOAD(QueueAudio);
    LOAD(PauseAudioDevice);
    LOAD(GetQueuedAudioSize);
    LOAD(Delay);
    LOAD(GetTicks64);
}

/* ---------------- emulator window state ---------------- */

static void *g_win = NULL;
static void *g_ren = NULL;
static void *g_tex = NULL;
static uint32_t g_audio = 0;
static int g_quit = 0;

/* SDL scancodes we care about */
#define SC_X 27
#define SC_Z 29
#define SC_ENTER 40
#define SC_BACKSPACE 42
#define SC_RIGHT 79
#define SC_LEFT 80
#define SC_DOWN 81
#define SC_UP 82
#define SC_RSHIFT 229
#define SC_F1 58
#define SC_Q 20
#define SC_W 26

/* ---------------- Lean entry points ---------------- */

/* open : UInt32 (scale) -> IO UInt32; 0 = ok, 1 = no SDL, 2+ = SDL error */
lean_obj_res gb_open(uint32_t scale, lean_obj_arg _w) {
    (void)_w;
    sdl_load();
    if (!sdl_ok || !sdl_handle) return lean_io_result_mk_ok(lean_box_uint32(1));
    if (g_win) return lean_io_result_mk_ok(lean_box_uint32(0));
    if (scale < 1) scale = 1;
    if (scale > 8) scale = 8;
    if (p_Init(0x30) != 0) return lean_io_result_mk_ok(lean_box_uint32(2));
    g_win = p_CreateWindow("lean-gameboy", 0x2FFF0000 /* centered */,
                           0x2FFF0000, FB_W * (int)scale, FB_H * (int)scale, 0);
    if (!g_win) return lean_io_result_mk_ok(lean_box_uint32(3));
    g_ren = p_CreateRenderer(g_win, -1, 0);
    if (!g_ren) return lean_io_result_mk_ok(lean_box_uint32(4));
    /* SDL_PIXELFORMAT_ARGB8888 = 0x16362004, SDL_TEXTUREACCESS_STREAMING = 1.
       (0x16462004 is RGBA8888 — using it swaps R/B on screen.) */
    g_tex = p_CreateTexture(g_ren, 0x16362004, 1, FB_W, FB_H);
    if (!g_tex) return lean_io_result_mk_ok(lean_box_uint32(5));
    /* audio: 44100 Hz, AUDIO_S16SYS (0x8010), mono */
    struct {
        int freq; uint16_t format; uint8_t channels; uint8_t silence;
        uint16_t samples; uint16_t padding; uint32_t size;
        void (*callback)(void); void *userdata;
    } want, have;
    memset(&want, 0, sizeof(want));
    memset(&have, 0, sizeof(have));
    want.freq = 44100;
    want.format = 0x8010;
    want.channels = 1;
    want.samples = 2048;
    g_audio = p_OpenAudioDevice(NULL, 0, &want, &have, 0);
    if (g_audio) p_PauseAudioDevice(g_audio, 0);
    return lean_io_result_mk_ok(lean_box_uint32(0));
}

/* blit : ByteArray (160*144*4 ARGB8888 LE) -> IO Unit */
lean_obj_res gb_blit(b_lean_obj_arg pixels, lean_obj_arg w) {
    if (g_tex && pixels) {
        size_t n = lean_sarray_size(pixels);
        if (n >= (size_t)(FB_W * FB_H * 4)) {
            const void *data = (const void *)lean_sarray_cptr(pixels);
            p_UpdateTexture(g_tex, NULL, data, FB_W * 4);
        }
    }
    (void)w;
    return lean_io_result_mk_ok(lean_box(0));
}

/* blit32 : Array UInt32 (160*144 ARGB8888 native order) -> IO Unit.
 * Unboxes Lean's boxed array into a scratch buffer and uploads it.
 * Faster than converting to bytes on the Lean side. */
static uint32_t *g_pxbuf = NULL;

lean_obj_res gb_blit32(b_lean_obj_arg arr, lean_obj_arg w) {
    (void)w;
    if (g_tex && arr) {
        size_t n = lean_array_size(arr);
        if (n >= (size_t)(FB_W * FB_H)) {
            if (!g_pxbuf) {
                g_pxbuf = (uint32_t *)malloc(sizeof(uint32_t) * FB_W * FB_H);
                if (!g_pxbuf) return lean_io_result_mk_ok(lean_box(0));
            }
            lean_object **objs = lean_array_cptr(arr);
            for (size_t i = 0; i < (size_t)(FB_W * FB_H); i++)
                g_pxbuf[i] = lean_unbox_uint32(objs[i]);
            p_UpdateTexture(g_tex, NULL, g_pxbuf, FB_W * 4);
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* ---- Game Boy Advance 240x160 path (separate window state) ---- */

#define AGB_W 240
#define AGB_H 160

static void *a_win = NULL;
static void *a_ren = NULL;
static void *a_tex = NULL;
static uint32_t *a_pxbuf = NULL;
static uint32_t a_audio = 0;

/* agb_open : UInt32 (scale) -> IO UInt32; same codes as gb_open */
lean_obj_res agb_open(uint32_t scale, lean_obj_arg _w) {
    (void)_w;
    sdl_load();
    if (!sdl_ok || !sdl_handle) return lean_io_result_mk_ok(lean_box_uint32(1));
    if (a_win) return lean_io_result_mk_ok(lean_box_uint32(0));
    if (scale < 1) scale = 1;
    if (scale > 8) scale = 8;
    if (p_Init(0x30) != 0) return lean_io_result_mk_ok(lean_box_uint32(2));
    a_win = p_CreateWindow("lean-agb", 0x2FFF0000 /* centered */,
                           0x2FFF0000, AGB_W * (int)scale, AGB_H * (int)scale, 0);
    if (!a_win) return lean_io_result_mk_ok(lean_box_uint32(3));
    a_ren = p_CreateRenderer(a_win, -1, 0);
    if (!a_ren) return lean_io_result_mk_ok(lean_box_uint32(4));
    a_tex = p_CreateTexture(a_ren, 0x16362004 /* ARGB8888 */, 1, AGB_W, AGB_H);
    if (!a_tex) return lean_io_result_mk_ok(lean_box_uint32(5));
    /* audio: GBA-native 32768 Hz, AUDIO_S16SYS (0x8010), stereo.
       4096-sample device buffer (~125 ms): scheduling jitter on a
       loaded host underruns smaller buffers faster than the emu can
       refill, which is heard as crackle; the cost is ~125 ms audio
       latency (standard emulator tradeoff). Failure is non-fatal
       (pushes become no-ops). */
    struct {
        int freq; uint16_t format; uint8_t channels; uint8_t silence;
        uint16_t samples; uint16_t padding; uint32_t size;
        void (*callback)(void); void *userdata;
    } want, have;
    memset(&want, 0, sizeof(want));
    memset(&have, 0, sizeof(have));
    want.freq = 32768;
    want.format = 0x8010;
    want.channels = 2;
    want.samples = 4096;
    a_audio = p_OpenAudioDevice(NULL, 0, &want, &have, 0);
    if (a_audio) p_PauseAudioDevice(a_audio, 0);
    return lean_io_result_mk_ok(lean_box_uint32(0));
}

/* agb_blit32 : Array UInt32 (240x160 ARGB8888) -> IO Unit */
lean_obj_res agb_blit32(b_lean_obj_arg arr, lean_obj_arg w) {
    (void)w;
    if (a_tex && arr) {
        size_t n = lean_array_size(arr);
        if (n >= (size_t)(AGB_W * AGB_H)) {
            if (!a_pxbuf) {
                a_pxbuf = (uint32_t *)malloc(sizeof(uint32_t) * AGB_W * AGB_H);
                if (!a_pxbuf) return lean_io_result_mk_ok(lean_box(0));
            }
            lean_object **objs = lean_array_cptr(arr);
            for (size_t i = 0; i < (size_t)(AGB_W * AGB_H); i++)
                a_pxbuf[i] = lean_unbox_uint32(objs[i]);
            p_UpdateTexture(a_tex, NULL, a_pxbuf, AGB_W * 4);
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* agb_present : IO Unit */
lean_obj_res agb_present(lean_obj_arg w) {
    if (a_ren && a_tex) {
        p_RenderClear(a_ren);
        p_RenderCopy(a_ren, a_tex, NULL, NULL);
        p_RenderPresent(a_ren);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* agb_audio : ByteArray (S16LE stereo) -> IO Unit */
lean_obj_res agb_audio(b_lean_obj_arg samples, lean_obj_arg w) {
    (void)w;
    if (a_audio && samples) {
        size_t n = lean_sarray_size(samples);
        /* cap queued audio at ~200ms (32768 Hz stereo); trim the frame
           instead of dropping it, mirroring gb_audio. Sized to absorb
           frame-cost variance (fast title frames vs dense scenes swing
           the queue ±26KB; a 100ms cap discarded the cushion that slow
           frames need, starving the device). Worst-case added latency
           after a stall is bounded by the cap. */
        uint32_t queued = p_GetQueuedAudioSize(a_audio);
        uint32_t cap = 32768 / 5 * 4;
        if (queued < cap && n > 0) {
            uint32_t room = cap - queued;
            uint32_t m = n < room ? (uint32_t)n : room;
            m &= ~3u; /* keep stereo-frame alignment */
            if (m > 0) {
                p_QueueAudio(a_audio,
                             (const void *)lean_sarray_cptr(samples),
                             m);
            }
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* agb_queued : IO UInt32 (queued-but-unplayed bytes, 0 w/o device). */
lean_obj_res agb_queued(lean_obj_arg w) {
    (void)w;
    uint32_t q = 0;
    if (a_audio) {
        q = p_GetQueuedAudioSize(a_audio);
    }
    return lean_io_result_mk_ok(lean_box_uint32(q));
}

/* agb_close : IO Unit (also releases the DMG window if open) */
lean_obj_res agb_close(lean_obj_arg w) {
    if (a_tex) { p_DestroyTexture(a_tex); a_tex = NULL; }
    if (a_ren) { p_DestroyRenderer(a_ren); a_ren = NULL; }
    if (a_win) { p_DestroyWindow(a_win); a_win = NULL; }
    if (a_audio) { p_CloseAudioDevice(a_audio); a_audio = 0; }
    if (a_pxbuf) { free(a_pxbuf); a_pxbuf = NULL; }
    return gb_close(w);
}

/* present : IO Unit */
lean_obj_res gb_present(lean_obj_arg w) {
    if (g_ren && g_tex) {
        p_RenderClear(g_ren);
        p_RenderCopy(g_ren, g_tex, NULL, NULL);
        p_RenderPresent(g_ren);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* poll : IO UInt32 — low 8 bits = buttons (R L U D A B Sel Sta),
 * bit 8 = quit requested, bit 9 = F1 (dump snapshot) requested,
 * bit 10 = L (Q key), bit 11 = R (W key) for GBA shoulders. */
lean_obj_res gb_poll(lean_obj_arg w) {
    uint32_t out = 0;
    if (!sdl_ok) return lean_io_result_mk_ok(lean_box_uint32(out));
    unsigned char ev[56];
    while (p_PollEvent(ev)) {
        uint32_t type = *(uint32_t *)ev;
        if (type == 0x100) g_quit = 1; /* SDL_QUIT */
    }
    int nkeys = 0;
    const uint8_t *st = p_GetKeyboardState(&nkeys);
    if (st && nkeys > SC_RSHIFT) {
        if (st[SC_RIGHT]) out |= 0x01;
        if (st[SC_LEFT]) out |= 0x02;
        if (st[SC_UP]) out |= 0x04;
        if (st[SC_DOWN]) out |= 0x08;
        if (st[SC_X]) out |= 0x10;
        if (st[SC_Z]) out |= 0x20;
        if (st[SC_RSHIFT] || st[SC_BACKSPACE]) out |= 0x40;
        if (st[SC_ENTER]) out |= 0x80;
        if (nkeys > SC_F1 && st[SC_F1]) out |= 0x200;
        if (nkeys > SC_W && st[SC_Q]) out |= 0x400;
        if (nkeys > SC_W && st[SC_W]) out |= 0x800;
    }
    if (g_quit) out |= 0x100;
    return lean_io_result_mk_ok(lean_box_uint32(out));
}

/* audio : ByteArray (S16LE mono) -> IO Unit */
lean_obj_res gb_audio(b_lean_obj_arg samples, lean_obj_arg w) {
    if (g_audio && samples) {
        size_t n = lean_sarray_size(samples);
        /* avoid unbounded latency: cap queued audio at ~100ms.
           Queue what fits instead of dropping the whole frame, so a
           transient overrun trims milliseconds (slight fast-forward)
           rather than punching a ~16ms hole (audible pop). */
        uint32_t queued = p_GetQueuedAudioSize(g_audio);
        uint32_t cap = 44100 / 10 * 2;
        if (queued < cap && n > 0) {
            uint32_t room = cap - queued;
            uint32_t m = n < room ? (uint32_t)n : room;
            m &= ~1u; /* keep S16 sample alignment */
            if (m > 0) {
                p_QueueAudio(g_audio,
                             (const void *)lean_sarray_cptr(samples),
                             m);
            }
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* delayMs : UInt32 -> IO Unit */
lean_obj_res gb_delay(uint32_t ms, lean_obj_arg w) {
    if (sdl_ok) p_Delay(ms);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ticksMs : IO UInt32 */
lean_obj_res gb_ticks(lean_obj_arg w) {
    uint32_t t = 0;
    if (sdl_ok) t = (uint32_t)p_GetTicks64();
    return lean_io_result_mk_ok(lean_box_uint32(t));
}

/* close : IO Unit */
lean_obj_res gb_close(lean_obj_arg w) {
    if (g_tex) { p_DestroyTexture(g_tex); g_tex = NULL; }
    if (g_ren) { p_DestroyRenderer(g_ren); g_ren = NULL; }
    if (g_audio) { p_CloseAudioDevice(g_audio); g_audio = 0; }
    if (g_win) { p_DestroyWindow(g_win); g_win = NULL; }
    if (sdl_ok) p_Quit();
    g_quit = 0;
    return lean_io_result_mk_ok(lean_box(0));
}
