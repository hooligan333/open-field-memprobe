// memprobe: does anything on the unit write into the DDR that OS 1.7.3 appears never to use?
//
// Reading the OS 1.7.3 image (open-field issue 15) gives two stretches of the 256 MiB of DDR that no boot record
// fills, no heap covers and no address in the code points into, though the firmware's own CPLB tables map them:
//   A  0x83800000 - 0x84000000   8 MiB, behind the C runtime's heap 1
//   B  0x84d30000 - 0x88000000   ~51 MiB, behind the image's zeroed data (a USB audio buffer of under 2.5 KiB sits
//                                just behind that data at 0x84d262a0, so B starts well clear of it)
//   C  0x88040000 - 0x8c000000   ~64 MiB. Version 3 leaves out 0x88000000 - 0x8803bfff: it is the display's second
//                                frame buffer (src/bf/display.cpp keeps its address in the data word 0x8401afc0 and
//                                clears 0x3c000 bytes of it), which version 2 found written while the screen changed.
//                                The first frame buffer is at 0x8c000000, just past C.
// This pack watches them in blocks of 64 KiB, a quarter of a block at each frame on the display thread (about
// 0.2 ms of work a frame; a pass over both takes some two minutes), and says in the log what it finds. Two modes:
//
//  READ (the default; nothing is written). The first pass takes a checksum of every 64 KiB block. Every later pass
//  takes them again and names each block whose checksum moved: something wrote there after the start. The block's
//  checksum is then taken anew, so a block written again and again is named again. Safe whatever lives there.
//
//  WRITE (the pack `memprobe-w`, built from this same file by memprobe_w.cpp). The first
//  pass fills both stretches with a pattern made from each word's own address. Every later pass checks every word
//  and names the first words that differ. This also shows the memory is there and holds what is written. If
//  something of the firmware did live there, this mode could disturb it: use it after READ has run clean for a
//  long session, and with the tape and sounds backed up.
//
// Version 2: the probe gives way while the unit is busy. A frame that comes more than SLOW_MS after the one before
// (the display slowed down, as while the tape records) is passed over with no work, so the probe never adds to a
// slow display. Nothing is missed by that: a write into a watched block stays there and the next look at the block
// sees it. The pass lines count the frames passed over.
//
// Log lines (tag `memprobe`): the mode at the start; the first pass's summary; a line for each pass during the
// first five and then every tenth, and for every pass that found a change; at most 32 lines naming a changed block
// or word over a start. A pass that finds nothing says so in its count.
//
// The mode is the pack's: copy memprobe.pack for READ or memprobe-w.pack for WRITE into the folder `packs`. When
// both are there, the READ pack stands aside and says so, and WRITE runs alone.
//
// Uses the base's op1f_log (level 1) and one function of the firmware, file_size at 0x8c051f9c (-1 when there is
// no such file), once, at the first frame, by the READ pack. Nothing is divided.

#include "build_m1_card.h"

typedef unsigned int u32;
#ifndef MEMPROBE_WRITE
typedef int (*FileSizeFn)(const char* path);
#define STOCK_FILE_SIZE ((FileSizeFn)0x8c051f9cu)
#endif

#ifdef MEMPROBE_WRITE
static const char LOG_FILE[] = "op1f/memprobe.cpp";      // the same tag, `memprobe`, in both packs
#define MEMPROBE_FRAME memprobe_w_frame
#define MEMPROBE_FRAME_NAME "memprobe_w_frame"
#else
static const char LOG_FILE[] = "op1f/memprobe.cpp";
static const char WRITE_PACK[] = "user/pk/memprobe-w.pack";  // the WRITE pack, in the folder `packs`
#define MEMPROBE_FRAME memprobe_frame
#define MEMPROBE_FRAME_NAME "memprobe_frame"
#endif

enum {
    A_START = 0x83800000u, A_END = 0x84000000u,
    B_START = 0x84d30000u, B_END = 0x88000000u,
    C_START = 0x88040000u, C_END = 0x8c000000u,
    BLOCK = 0x10000u,                                   // 64 KiB, one checksum each
    STEPS = 4, STEP_WORDS = BLOCK / 4 / STEPS,          // a quarter of a block, 16 KiB, a frame
    A_BLOCKS = (A_END - A_START) / BLOCK,               // 128
    B_BLOCKS = (B_END - B_START) / BLOCK,               // 813
    C_BLOCKS = (C_END - C_START) / BLOCK,               // 1020
    BLOCKS = A_BLOCKS + B_BLOCKS + C_BLOCKS,            // 1961
    NAMED_MOST = 32,                                    // lines naming a block or a word, over a start
    WORDS_NAMED_A_BLOCK = 2,
    SLOW_MS = 25                                        // a frame later than this after the one before: no work
};
static const u32 PATTERN_KEY = 0x5a3cc3a5u;

static u32 sums[BLOCKS];                                // READ: each block's checksum as last taken
static struct {
    int started, write, aside;
    u32 block, step, pass;                              // the block and quarter of this frame, the pass (0 = the first)
    u32 hash, zeros, bad;
    u32 last_ms, skipped;                               // the clock at the frame before; frames passed over in this pass                               // the block's checksum so far, its zero words, its words that differ
    u32 pass_changed, total_changed, named, zero_words, pass_ms;
} st;

static inline volatile u32* block_at(u32 i) {
    if (i < A_BLOCKS) return (volatile u32*)(A_START + i * BLOCK);
    i -= A_BLOCKS;
    if (i < B_BLOCKS) return (volatile u32*)(B_START + i * BLOCK);
    return (volatile u32*)(C_START + (i - B_BLOCKS) * BLOCK);
}
static inline u32 pattern(u32 address) { return address ^ PATTERN_KEY; }

// One quarter of a block into the running checksum.
static void checksum_step(volatile u32* p, u32 first) {
    u32 h = st.hash, z = 0;
    for (u32 k = first; k < first + STEP_WORDS; ++k) {
        u32 w = p[k];
        z += (w == 0);
        h = ((h << 5) | (h >> 27)) ^ (w + k);
    }
    st.zeros += z;
    st.hash = h;
}

static void first_frame(unsigned ms) {
    st.started = 1;
    st.pass_ms = ms;
#ifdef MEMPROBE_WRITE
    st.write = 1;
#else
    st.write = 0;
    if (STOCK_FILE_SIZE(WRITE_PACK) >= 0) {
        st.aside = 1;
        op1f_log(3, LOG_FILE, 6, "memprobe 3: memprobe-w.pack is in packs too: this READ pack stands aside and WRITE runs alone");
        return;
    }
#endif
    op1f_log(3, LOG_FILE, 1, "memprobe 3: mode %s; watching 0x%08x-0x%08x, 0x%08x-0x%08x and 0x%08x-0x%08x, %u blocks of 64 KiB, a quarter a frame",
             st.write ? "WRITE (pattern, every word checked)" : "READ (checksums only, nothing written)",
             (u32)A_START, (u32)A_END, (u32)B_START, (u32)B_END, (u32)C_START, (u32)C_END, (u32)BLOCKS);
}

static void name_block(u32 i, u32 before, u32 now) {
    if (st.named >= NAMED_MOST) return;
    ++st.named;
    op1f_log(2, LOG_FILE, 2, "memprobe: block 0x%08x (64 KiB) changed in pass %u: checksum %08x -> %08x",
             (u32)block_at(i), st.pass, before, now);
}

static void read_frame(u32 i, u32 first, int last) {
    if (first == 0) { st.hash = 0x811c9dc5u; st.zeros = 0; }
    checksum_step(block_at(i), first);
    if (!last) return;
    u32 now = st.hash;
    if (st.pass == 0) { sums[i] = now; st.zero_words += st.zeros; return; }
    if (now != sums[i]) { ++st.pass_changed; name_block(i, sums[i], now); sums[i] = now; }
}

static void write_frame(u32 i, u32 first, int last) {
    volatile u32* p = block_at(i);
    u32 base = (u32)p, named_here = 0;
    if (st.pass == 0) {
        for (u32 k = first; k < first + STEP_WORDS; ++k) p[k] = pattern(base + 4 * k);
        return;
    }
    if (first == 0) st.bad = 0;
    u32 bad = 0;
    for (u32 k = first; k < first + STEP_WORDS; ++k) {
        u32 want = pattern(base + 4 * k), got = p[k];
        if (got == want) continue;
        ++bad;
        if (named_here < WORDS_NAMED_A_BLOCK && st.named < NAMED_MOST) {
            ++named_here; ++st.named;
            op1f_log(2, LOG_FILE, 3, "memprobe: word 0x%08x holds %08x, not the pattern %08x (pass %u)", base + 4 * k, got, want, st.pass);
        }
        p[k] = want;                                    // put the pattern back, to see whether it is written again
    }
    st.bad += bad;
    if (last && st.bad) ++st.pass_changed;
}

static void end_of_pass(unsigned ms) {
    u32 took = ms - st.pass_ms;
    if (st.pass == 0) {
        if (st.write)
            op1f_log(3, LOG_FILE, 4, "memprobe: pattern written over all %u blocks in %u ms (%u slow frames passed over)", (u32)BLOCKS, took, st.skipped);
        else
            op1f_log(3, LOG_FILE, 4, "memprobe: first checksums of %u blocks taken in %u ms (%u slow frames passed over); %u of %u words were 0",
                     (u32)BLOCKS, took, st.skipped, st.zero_words, (u32)(BLOCKS * (BLOCK / 4)));
    } else {
        st.total_changed += st.pass_changed;
        u32 p = st.pass, tenth = p;
        while (tenth >= 10) tenth -= 10;
        if (p <= 5 || tenth == 0 || st.pass_changed)
            op1f_log(st.pass_changed ? 2 : 3, LOG_FILE, 5, "memprobe: pass %u done in %u ms (%u slow frames passed over), %u block(s) changed in it, %u in all since the start",
                     p, took, st.skipped, st.pass_changed, st.total_changed);
    }
    st.pass_changed = 0;
    st.skipped = 0;
    st.pass_ms = ms;
    ++st.pass;
}

extern "C" void MEMPROBE_FRAME(const Op1fFrame* now) OP1F_NAMED(MEMPROBE_FRAME_NAME);

void MEMPROBE_FRAME(const Op1fFrame* now) {
    if (!st.started) { first_frame(now->ms); st.last_ms = now->ms; }
    if (st.aside) return;
    u32 gap = now->ms - st.last_ms;
    st.last_ms = now->ms;
    if (gap > (u32)SLOW_MS) { ++st.skipped; return; }
    u32 i = st.block, first = st.step * STEP_WORDS;
    int last = st.step == STEPS - 1;
    if (st.write) write_frame(i, first, last); else read_frame(i, first, last);
    if (!last) { ++st.step; return; }
    st.step = 0;
    if (++st.block == BLOCKS) { st.block = 0; end_of_pass(now->ms); }
}
