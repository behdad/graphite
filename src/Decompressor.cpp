// SPDX-License-Identifier: MIT OR MPL-2.0 OR LGPL-2.1-or-later OR GPL-2.0-or-later
// Copyright 2015, SIL International, All rights reserved.

#include <cassert>

#include "inc/Decompressor.h"
#include "inc/Compression.h"

using namespace lz4;

namespace {

// The size of the words short runs are copied in, on every machine.
size_t const WORD = sizeof(u64);

inline
u32 read_literal(u8 const * &s, u8 const * const e, u32 l) {
    if (l == 15 && s != e)
    {
        u8 b = 0;
        do { l += b = *s++; } while(b==0xff && s != e);
    }
    return l;
}

bool read_sequence(u8 const * &src, u8 const * const end, u8 const * &literal,
                    u32 & literal_len, u32 & match_len, u32 & match_dist)
{
    u8 const token = *src++;

    literal_len = read_literal(src, end, token >> 4);
    literal = src;
    src += literal_len;

    // Normal exit for end of stream, wrap arround check and parital match check.
    if (src > end - sizeof(u16) || src < literal)
        return false;

    match_dist  = *src++;
    match_dist |= *src++ << 8;
    match_len = read_literal(src, end, token & 0xf) + MINMATCH;

    // Malformed stream check.
    return src <= end-MINCODA;
}

// Copy a match of n bytes to d from s, which is before d, when there is
// room for at least room bytes at d.
inline
u8 * copy_match(u8 * const d, u8 const * const s, const size_t n, const size_t room)
{
    if (n <= 2*WORD && size_t(d - s) >= WORD && room >= 2*WORD)
    {
        // A short match at least a word back: two whole words, the
        // second of which may read what the first one wrote.
        unaligned_copy<WORD>(d, s);
        unaligned_copy<WORD>(d + WORD, s + WORD);
        return d + n;
    }
    if (size_t(d - s) >= n)
    {
        memcpy(d, s, n);
        return d + n;
    }
    return repeat_copy(d, s, n);
}

// A sequence that has a literal of fewer than 15 bytes and a match length
// of at most one extension byte takes at most FAST_SRC - MINCODA bytes of
// source and makes at most FAST_DST - LASTLITERALS bytes of output. With
// FAST_SRC bytes of source left and between FAST_DST and FAST_DST_MAX of
// output none of the tests on such a sequence in read_sequence() or on its
// lengths in decompress() can fail, and the casts to unsigned there change
// nothing.
size_t const FAST_SRC     = 1 + 14 + 2 + 1 + MINCODA,
             FAST_DST     = 14 + 15 + 254 + MINMATCH + LASTLITERALS,
             FAST_DST_MAX = size_t(unsigned(-1));

}

int lz4::decompress(void const *in, size_t in_size, void *out, size_t out_size)
{
    if (out_size <= in_size || in_size < MINSRCSIZE)
        return -1;

    u8 const *       src     = static_cast<u8 const *>(in),
             *       literal = 0,
             * const src_end = src + in_size;

    u8 *       dst     = static_cast<u8*>(out),
       * const dst_end = dst + out_size;

    // Check the in and out size hasn't wrapped around.
    if (src >= src_end || dst >= dst_end)
        return -1;

    u32 literal_len = 0,
        match_len = 0,
        match_dist = 0;

    for (;;)
    {
        if (size_t(src_end - src) >= FAST_SRC && out_size - FAST_DST <= FAST_DST_MAX - FAST_DST)
        {
            u8 const token = *src;
            u32 const lit  = token >> 4;
            u32       len  = token & 0xf;
            if (lit != 15 && (len != 15 || src[lit + 3] != 0xff))
            {
                // Away from the ends of both buffers such a sequence only
                // needs its match to start inside the output. The literal
                // is copied as two words whatever its length.
                unaligned_copy<WORD>(dst, src + 1);
                unaligned_copy<WORD>(dst + WORD, src + 1 + WORD);
                dst += lit;
                out_size -= lit;
                src += 1 + lit;

                u32 dist = *src++;
                dist    |= *src++ << 8;
                if (len == 15) len += *src++;
                len += MINMATCH;

                u8 const * const pcpy = dst - dist;
                if (pcpy < static_cast<u8*>(out) || pcpy >= dst)
                    return -1;
                dst = copy_match(dst, pcpy, len, FAST_DST - 14);
                out_size -= len;
                continue;
            }
        }

        if (!read_sequence(src, src_end, literal, literal_len, match_len,
                           match_dist))
            break;

        if (literal_len != 0)
        {
            // Copy in literal. At this point the a minimal literal + minminal
            // match plus the coda (1 + 2 + 5) must be 8 bytes or more allowing
            // us to remain within the src buffer when copying a whole word
            // for a literal that is no longer than one.
            if (align(literal_len) > out_size)
                return -1;
            if (literal_len <= WORD && out_size >= WORD)
                unaligned_copy<WORD>(dst, literal);
            else
                memcpy(dst, literal, literal_len);
            dst += literal_len;
            out_size -= literal_len;
        }

        // Copy, possibly repeating, match from earlier in the
        //  decoded output.
        u8 const * const pcpy = dst - match_dist;
        if (pcpy < static_cast<u8*>(out)
              || match_len > unsigned(out_size - LASTLITERALS)
              // Wrap around checks:
              || out_size < LASTLITERALS || pcpy >= dst)
            return -1;
        dst = copy_match(dst, pcpy, match_len, out_size);
        out_size -= match_len;
    }

    if (literal > src_end - literal_len || literal_len > out_size)
        return -1;
    memcpy(dst, literal, literal_len);
    dst += literal_len;

    return int(dst - (u8*)out);
}
