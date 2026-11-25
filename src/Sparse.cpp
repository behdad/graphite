// SPDX-License-Identifier: MIT OR MPL-2.0 OR LGPL-2.1-or-later OR GPL-2.0-or-later
// Copyright 2011, SIL International, All rights reserved.

#include <cassert>
#include "inc/Sparse.h"
#include "inc/bits.h"

using namespace graphite2;

const sparse::chunk sparse::empty_chunk = {0,0};

sparse::~sparse() throw()
{
    if (m_array.map == &empty_chunk) return;
    free(m_array.values);
}


size_t sparse::capacity() const throw()
{
    size_t n = m_nchunks,
           s = 0;

    for (const chunk *ci=m_array.map; n; --n, ++ci)
        s += bit_set_count(ci->mask);

    return s;
}
