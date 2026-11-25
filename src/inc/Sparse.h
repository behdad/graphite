// SPDX-License-Identifier: MIT OR MPL-2.0 OR LGPL-2.1-or-later OR GPL-2.0-or-later
// Copyright 2011, SIL International, All rights reserved.

#pragma once
#include <iterator>
#include <utility>

#include "inc/Main.h"
#include "inc/bits.h"

namespace graphite2 {


// A read-only packed fast sparse array of uint16 with uint16 keys.
// Like most container classes this has capacity and size properties and these
// refer to the number of stored entries and the number of addressable entries
// as normal. However due the sparse nature the capacity is always <= than the
// size.
class sparse
{
public:
    typedef uint16  key_type;
    typedef uint16  mapped_type;
    typedef std::pair<const key_type, mapped_type> value_type;

private:
    typedef unsigned long   mask_t;

    static const unsigned char  SIZEOF_CHUNK = (sizeof(mask_t) - sizeof(key_type))*8;

    struct chunk
    {
        mask_t          mask:SIZEOF_CHUNK;
        key_type        offset;
    };

    static const chunk  empty_chunk;
    sparse(const sparse &);
    sparse & operator = (const sparse &);

public:
    // Sequential access to the values of consecutive keys: constructed at a
    // key k, each call to next() returns what operator[] would return for
    // k, k+1, k+2, ... in turn, without redoing the chunk lookup and the
    // population count for every key.
    class reader;

    template<typename I>
    sparse(I first, const I last);
    sparse() throw();
    ~sparse() throw();

    operator bool () const throw();
    mapped_type     operator [] (const key_type k) const throw();

    size_t capacity() const throw();
    size_t size()     const throw();

    size_t _sizeof() const throw();

    CLASS_NEW_DELETE;

private:
    union {
        chunk         * map;
        mapped_type   * values;
    }           m_array;
    key_type    m_nchunks;
};


inline
sparse::sparse() throw() : m_nchunks(0)
{
    m_array.map = const_cast<graphite2::sparse::chunk *>(&empty_chunk);
}


template <typename I>
sparse::sparse(I attr, const I last)
: m_nchunks(0)
{
    m_array.map = 0;

    // Find the maximum extent of the key space.
    size_t n_values=0;
    long lastkey = -1;
    for (I i = attr; i != last; ++i, ++n_values)
    {
        const typename std::iterator_traits<I>::value_type v = *i;
        if (v.second == 0)      { --n_values; continue; }
        if (v.first <= lastkey) { m_nchunks = 0; return; }

        lastkey = v.first;
        const key_type k = v.first / SIZEOF_CHUNK;
        if (k >= m_nchunks) m_nchunks = k+1;
    }
    if (m_nchunks == 0)
    {
        m_array.map=const_cast<graphite2::sparse::chunk *>(&empty_chunk);
        return;
    }

    m_array.values = grzeroalloc<mapped_type>((m_nchunks*sizeof(chunk) + sizeof(mapped_type)-1)
                                                 / sizeof(mapped_type)
                                                 + n_values);

    if (m_array.values == 0)
        return;

    // coverity[forward_null : FALSE] Since m_array is union and m_array.values is not NULL
    chunk * ci = m_array.map;
    ci->offset = (m_nchunks*sizeof(chunk) + sizeof(mapped_type)-1)/sizeof(mapped_type);
    mapped_type * vi = m_array.values + ci->offset;
    for (; attr != last; ++attr, ++vi)
    {
        const typename std::iterator_traits<I>::value_type v = *attr;
        if (v.second == 0)  { --vi; continue; }

        chunk * const ci_ = m_array.map + v.first/SIZEOF_CHUNK;

        if (ci != ci_)
        {
            ci = ci_;
            ci->offset = key_type(vi - m_array.values);
        }

        ci->mask |= 1UL << (SIZEOF_CHUNK - 1 - (v.first % SIZEOF_CHUNK));
        *vi = v.second;
    }
}


inline
sparse::operator bool () const throw()
{
    return m_array.map != 0;
}

inline
sparse::mapped_type sparse::operator [] (const key_type k) const throw()
{
    const unsigned int  n = k/SIZEOF_CHUNK;
    if (n >= m_nchunks) return 0;       // beyond the last key stored

    const chunk &       c = m_array.map[n];
    const mask_t        m = c.mask >> (SIZEOF_CHUNK - 1 - (k%SIZEOF_CHUNK));
    if (!(m & 1))       return 0;       // key not present

    return m_array.values[c.offset + bit_set_count(mask_t(m >> 1))];
}

inline
size_t sparse::size() const throw()
{
    return m_nchunks*SIZEOF_CHUNK;
}

inline
size_t sparse::_sizeof() const throw()
{
    return sizeof(sparse) + capacity()*sizeof(mapped_type) + m_nchunks*sizeof(chunk);
}


class sparse::reader
{
public:
    reader(const sparse & s, const key_type k) throw();

    mapped_type next() throw();

private:
    void        next_chunk() throw();

    const sparse      & m_sparse;
    const mapped_type * m_value;    // value of the next key present in this chunk
    mask_t              m_mask;     // this chunk's mask, the next key's bit moved to the top
    unsigned int        m_left,     // keys left in this chunk
                        m_chunk;    // index of the next chunk
};

inline
void sparse::reader::next_chunk() throw()
{
    if (m_chunk < m_sparse.m_nchunks)
    {
        const chunk & c = m_sparse.m_array.map[m_chunk];
        m_mask  = c.mask;
        m_value = m_sparse.m_array.values + c.offset;
    }
    else
        m_mask = 0;     // past the end every key is absent
    m_left = SIZEOF_CHUNK;
    ++m_chunk;
}

inline
sparse::reader::reader(const sparse & s, const key_type k) throw()
: m_sparse(s), m_value(0), m_mask(0), m_left(0), m_chunk(k/SIZEOF_CHUNK)
{
    const unsigned int skip = k%SIZEOF_CHUNK;

    next_chunk();
    // Step over the keys of this chunk that come before k.
    m_value += bit_set_count(mask_t(m_mask >> (SIZEOF_CHUNK - skip)));
    m_mask <<= skip;
    m_left  -= skip;
}

inline
sparse::mapped_type sparse::reader::next() throw()
{
    if (m_left == 0) next_chunk();
    --m_left;

    const mask_t present = m_mask & (mask_t(1) << (SIZEOF_CHUNK - 1));
    m_mask <<= 1;
    return present ? *m_value++ : mapped_type(0);
}

} // namespace graphite2
