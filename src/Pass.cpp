// SPDX-License-Identifier: MIT OR MPL-2.0 OR LGPL-2.1-or-later OR GPL-2.0-or-later
// Copyright 2010, SIL International, All rights reserved.

#include "inc/Main.h"
#include "inc/debug.h"
#include "inc/Endian.h"
#include "inc/Pass.h"
#include <cstring>
#include <cstdlib>
#include <cassert>
#include <cmath>
#include "inc/Segment.h"
#include "inc/Code.h"
#include "inc/Rule.h"
#include "inc/Error.h"
#include "inc/Collider.h"

using namespace graphite2;
using vm::Machine;
typedef Machine::Code  Code;

enum KernCollison
{
    None       = 0,
    CrossSpace = 1,
    InWord     = 2,
    reserved   = 3
};

Pass::Pass()
: m_silf(0),
  m_cols(0),
  m_rules(0),
  m_ruleMap(0),
  m_startStates(0),
  m_transitions(0),
  m_states(0),
  m_codes(0),
  m_progs(0),
  m_filter(0),
  m_filterPairs(0),
  m_context(0),
  m_numCollRuns(0),
  m_kernColls(0),
  m_iMaxLoop(0),
  m_numGlyphs(0),
  m_numRules(0),
  m_numStates(0),
  m_numTransition(0),
  m_numSuccess(0),
  m_successStart(0),
  m_numColumns(0),
  m_filterWords(0),
  m_atCursor(0),
  m_minPreCtxt(0),
  m_maxPreCtxt(0),
  m_colThreshold(0),
  m_isReverseDir(false)
{
}

Pass::~Pass()
{
    free(m_cols);
    free(m_startStates);
    free(m_transitions);
    free(m_states);
    free(m_ruleMap);

    if (m_rules) delete [] m_rules;
    if (m_codes) delete [] m_codes;
    free(m_progs);
    free(m_filter);
    free(m_filterPairs);
    free(m_context);
}

bool Pass::readPass(const byte * const pass_start, size_t pass_length, size_t subtable_base,
        GR_MAYBE_UNUSED Face & face, passtype pt, GR_MAYBE_UNUSED uint32 version, Error &e)
{
    const byte * p              = pass_start,
               * const pass_end = p + pass_length;
    size_t numRanges;

    if (e.test(pass_length < 40, E_BADPASSLENGTH)) return face.error(e);
    // Read in basic values
    const byte flags = be::read<byte>(p);
    if (e.test((flags & 0x1f) &&
            (pt < PASS_TYPE_POSITIONING || !m_silf->aCollision() || !face.glyphs().hasBoxes() || !(m_silf->flags() & 0x20)),
            E_BADCOLLISIONPASS))
        return face.error(e);
    m_numCollRuns = flags & 0x7;
    m_kernColls   = (flags >> 3) & 0x3;
    m_isReverseDir = (flags >> 5) & 0x1;
    m_iMaxLoop = be::read<byte>(p);
    if (m_iMaxLoop < 1) m_iMaxLoop = 1;
    be::skip<byte>(p,2); // skip maxContext & maxBackup
    m_numRules = be::read<uint16>(p);
    if (e.test(!m_numRules && m_numCollRuns == 0, E_BADEMPTYPASS)) return face.error(e);
    be::skip<uint16>(p);   // fsmOffset - not sure why we would want this
    const byte * const pcCode = pass_start + be::read<uint32>(p) - subtable_base,
               * const rcCode = pass_start + be::read<uint32>(p) - subtable_base,
               * const aCode  = pass_start + be::read<uint32>(p) - subtable_base;
    be::skip<uint32>(p);
    m_numStates = be::read<uint16>(p);
    m_numTransition = be::read<uint16>(p);
    m_numSuccess = be::read<uint16>(p);
    m_numColumns = be::read<uint16>(p);
    numRanges = be::read<uint16>(p);
    be::skip<uint16>(p, 3); // skip searchRange, entrySelector & rangeShift.
    assert(p - pass_start == 40);
    // Perform some sanity checks.
    if ( e.test(m_numTransition > m_numStates, E_BADNUMTRANS)
            || e.test(m_numSuccess > m_numStates, E_BADNUMSUCCESS)
            || e.test(m_numSuccess + m_numTransition < m_numStates, E_BADNUMSTATES)
            || e.test(m_numRules && numRanges == 0, E_NORANGES)
            || e.test(m_numColumns > 0x7FFF, E_BADNUMCOLUMNS))
        return face.error(e);

    m_successStart = m_numStates - m_numSuccess;
    // test for beyond end - 1 to account for reading uint16
    if (e.test(p + numRanges * 6 - 2 > pass_end, E_BADPASSLENGTH)) return face.error(e);
    m_numGlyphs = be::peek<uint16>(p + numRanges * 6 - 4) + 1;
    // Calculate the start of various arrays.
    const byte * const ranges = p;
    be::skip<uint16>(p, numRanges*3);
    const byte * const o_rule_map = p;
    be::skip<uint16>(p, m_numSuccess + 1);

    // More sanity checks
    if (e.test(reinterpret_cast<const byte *>(o_rule_map + m_numSuccess*sizeof(uint16)) > pass_end
            || p > pass_end, E_BADRULEMAPLEN))
        return face.error(e);
    const size_t numEntries = be::peek<uint16>(o_rule_map + m_numSuccess*sizeof(uint16));
    const byte * const   rule_map = p;
    be::skip<uint16>(p, numEntries);

    if (e.test(p + 2*sizeof(uint8) > pass_end, E_BADPASSLENGTH)) return face.error(e);
    m_minPreCtxt = be::read<uint8>(p);
    m_maxPreCtxt = be::read<uint8>(p);
    if (e.test(m_minPreCtxt > m_maxPreCtxt, E_BADCTXTLENBOUNDS)) return face.error(e);
    const byte * const start_states = p;
    be::skip<int16>(p, m_maxPreCtxt - m_minPreCtxt + 1);
    const uint16 * const sort_keys = reinterpret_cast<const uint16 *>(p);
    be::skip<uint16>(p, m_numRules);
    const byte * const precontext = p;
    be::skip<byte>(p, m_numRules);

    if (e.test(p + sizeof(uint16) + sizeof(uint8) > pass_end, E_BADCTXTLENS)) return face.error(e);
    m_colThreshold = be::read<uint8>(p);
    if (m_colThreshold == 0) m_colThreshold = 10;       // A default
    const size_t pass_constraint_len = be::read<uint16>(p);

    const uint16 * const o_constraint = reinterpret_cast<const uint16 *>(p);
    be::skip<uint16>(p, m_numRules + 1);
    const uint16 * const o_actions = reinterpret_cast<const uint16 *>(p);
    be::skip<uint16>(p, m_numRules + 1);
    const byte * const states = p;
    if (e.test(2u*m_numTransition*m_numColumns >= (unsigned)(pass_end - p), E_BADPASSLENGTH)
            || e.test(p >= pass_end, E_BADPASSLENGTH))
        return face.error(e);
    be::skip<int16>(p, m_numTransition*m_numColumns);
    be::skip<uint8>(p);
    if (e.test(p != pcCode, E_BADPASSCCODEPTR)) return face.error(e);
    be::skip<byte>(p, pass_constraint_len);
    if (e.test(p != rcCode, E_BADRULECCODEPTR)
        || e.test(size_t(rcCode - pcCode) != pass_constraint_len, E_BADCCODELEN)) return face.error(e);
    be::skip<byte>(p, be::peek<uint16>(o_constraint + m_numRules));
    if (e.test(p != aCode, E_BADACTIONCODEPTR)) return face.error(e);
    be::skip<byte>(p, be::peek<uint16>(o_actions + m_numRules));

    // We should be at the end or within the pass
    if (e.test(p > pass_end, E_BADPASSLENGTH)) return face.error(e);

    // Load the pass constraint if there is one.
    if (pass_constraint_len)
    {
        face.error_context(face.error_context() + 1);
        m_cPConstraint = vm::Machine::Code(true, pcCode, pcCode + pass_constraint_len,
                                  precontext[0], be::peek<uint16>(sort_keys), *m_silf, face, PASS_TYPE_UNKNOWN);
        if (e.test(!m_cPConstraint, E_OUTOFMEM)
                || e.test(m_cPConstraint.status() != Code::loaded, int(m_cPConstraint.status()) + E_CODEFAILURE))
            return face.error(e);
        face.error_context(face.error_context() - 1);
    }
    if (m_numRules)
    {
        if (!readRanges(ranges, numRanges, e)) return face.error(e);
        if (!readRules(rule_map, numEntries,  precontext, sort_keys,
                   o_constraint, rcCode, o_actions, aCode, face, pt, e)) return false;
    }
#ifdef GRAPHITE2_TELEMETRY
    telemetry::category _states_cat(face.tele.states);
#endif
    if (!m_numRules) return true;
    return readStates(start_states, states, o_rule_map, face, e) && buildFilter(ranges, numRanges, face, e);
}


bool Pass::readRules(const byte * rule_map, const size_t num_entries,
                     const byte *precontext, const uint16 * sort_key,
                     const uint16 * o_constraint, const byte *rc_data,
                     const uint16 * o_action,     const byte * ac_data,
                     Face & face, passtype pt, Error &e)
{
    const byte * const ac_data_end = ac_data + be::peek<uint16>(o_action + m_numRules);
    const byte * const rc_data_end = rc_data + be::peek<uint16>(o_constraint + m_numRules);

    precontext += m_numRules;
    sort_key   += m_numRules;
    o_constraint += m_numRules;
    o_action += m_numRules;

    // Load rules.
    const byte * ac_begin = 0, * rc_begin = 0,
               * ac_end = ac_data + be::peek<uint16>(o_action),
               * rc_end = rc_data + be::peek<uint16>(o_constraint);

    // Allocate pools
    m_rules = new Rule [m_numRules];
    m_codes = new Code [m_numRules*2];
    int totalSlots = 0;
    const uint16 *tsort = sort_key;
    for (int i = 0; i < m_numRules; ++i)
        totalSlots += be::peek<uint16>(--tsort);
    const size_t prog_pool_sz = vm::Machine::Code::estimateCodeDataOut(ac_end - ac_data + rc_end - rc_data, 2 * m_numRules, totalSlots);
    m_progs = gralloc<byte>(prog_pool_sz);
    byte * prog_pool_free = m_progs,
         * prog_pool_end  = m_progs + prog_pool_sz;
    if (e.test(!(m_rules && m_codes && m_progs), E_OUTOFMEM)) return face.error(e);

    Rule * r = m_rules + m_numRules - 1;
    for (size_t n = m_numRules; r >= m_rules; --n, --r, ac_end = ac_begin, rc_end = rc_begin)
    {
        face.error_context((face.error_context() & 0xFFFF00) + EC_ARULE + int((n - 1) << 24));
        r->preContext = *--precontext;
        r->sort       = be::peek<uint16>(--sort_key);
#ifndef NDEBUG
        r->rule_idx   = uint16(n - 1);
#endif
        if (r->sort > 63 || r->preContext >= r->sort || r->preContext > m_maxPreCtxt || r->preContext < m_minPreCtxt)
            return false;
        ac_begin      = ac_data + be::peek<uint16>(--o_action);
        --o_constraint;
        rc_begin      = be::peek<uint16>(o_constraint) ? rc_data + be::peek<uint16>(o_constraint) : rc_end;

        if (ac_begin > ac_end || ac_begin > ac_data_end || ac_end > ac_data_end
                || rc_begin > rc_end || rc_begin > rc_data_end || rc_end > rc_data_end
                || vm::Machine::Code::estimateCodeDataOut(ac_end - ac_begin + rc_end - rc_begin, 2, r->sort) > size_t(prog_pool_end - prog_pool_free))
            return false;
        r->action     = new (m_codes+n*2-2) vm::Machine::Code(false, ac_begin, ac_end, r->preContext, r->sort, *m_silf, face, pt, &prog_pool_free);
        r->constraint = new (m_codes+n*2-1) vm::Machine::Code(true,  rc_begin, rc_end, r->preContext, r->sort, *m_silf, face, pt, &prog_pool_free);

        if (e.test(!r->action || !r->constraint, E_OUTOFMEM)
                || e.test(r->action->status() != Code::loaded, int(r->action->status()) + E_CODEFAILURE)
                || e.test(r->constraint->status() != Code::loaded, int(r->constraint->status()) + E_CODEFAILURE)
                || e.test(!r->constraint->immutable(), E_MUTABLECCODE))
            return face.error(e);
    }

    byte * const moved_progs = prog_pool_free > m_progs ? static_cast<byte *>(realloc(m_progs, prog_pool_free - m_progs)) : 0;
    if (e.test(!moved_progs, E_OUTOFMEM))
    {
        free(m_progs);
        m_progs = 0;
        return face.error(e);
    }

    if (moved_progs != m_progs)
    {
        for (Code * c = m_codes, * const ce = c + m_numRules*2; c != ce; ++c)
        {
            c->externalProgramMoved(moved_progs - m_progs);
        }
        m_progs = moved_progs;
    }

    // Load the rule entries map
    face.error_context((face.error_context() & 0xFFFF00) + EC_APASS);
    //TODO: Coverity: 1315804: FORWARD_NULL
    RuleEntry * re = m_ruleMap = gralloc<RuleEntry>(num_entries);
    if (e.test(!re, E_OUTOFMEM)) return face.error(e);
    for (size_t n = num_entries; n; --n, ++re)
    {
        const ptrdiff_t rn = be::read<uint16>(rule_map);
        if (e.test(rn >= m_numRules, E_BADRULENUM))  return face.error(e);
        re->rule = m_rules + rn;
    }

    return true;
}

static int cmpRuleEntry(const void *a, const void *b) { return (*(RuleEntry *)a < *(RuleEntry *)b ? -1 :
                                                                (*(RuleEntry *)b < *(RuleEntry *)a ? 1 : 0)); }

bool Pass::readStates(const byte * starts, const byte *states, const byte * o_rule_map, GR_MAYBE_UNUSED Face & face, Error &e)
{
#ifdef GRAPHITE2_TELEMETRY
    telemetry::category _states_cat(face.tele.starts);
#endif
    m_startStates = gralloc<uint16>(m_maxPreCtxt - m_minPreCtxt + 1);
#ifdef GRAPHITE2_TELEMETRY
    telemetry::set_category(face.tele.states);
#endif
    m_states      = gralloc<State>(m_numStates);
#ifdef GRAPHITE2_TELEMETRY
    telemetry::set_category(face.tele.transitions);
#endif
    m_transitions      = gralloc<uint16>(m_numTransition * m_numColumns);

    if (e.test(!m_startStates || !m_states || !m_transitions, E_OUTOFMEM)) return face.error(e);
    // load start states
    for (uint16 * s = m_startStates,
                * const s_end = s + m_maxPreCtxt - m_minPreCtxt + 1; s != s_end; ++s)
    {
        *s = be::read<uint16>(starts);
        if (e.test(*s >= m_numStates, E_BADSTATE))
        {
            face.error_context((face.error_context() & 0xFFFF00) + EC_ASTARTS + int((s - m_startStates) << 24));
            return face.error(e); // true;
        }
    }

    // load state transition table.
    for (uint16 * t = m_transitions,
                * const t_end = t + m_numTransition*m_numColumns; t != t_end; ++t)
    {
        *t = be::read<uint16>(states);
        if (e.test(*t >= m_numStates, E_BADSTATE))
        {
            face.error_context((face.error_context() & 0xFFFF00) + EC_ATRANS + int(((t - m_transitions) / m_numColumns) << 8));
            return face.error(e);
        }
    }

    State * s = m_states,
          * const success_begin = m_states + m_numStates - m_numSuccess;
    const RuleEntry * rule_map_end = m_ruleMap + be::peek<uint16>(o_rule_map + m_numSuccess*sizeof(uint16));
    for (size_t n = m_numStates; n; --n, ++s)
    {
        RuleEntry * const begin = s < success_begin ? 0 : m_ruleMap + be::read<uint16>(o_rule_map),
                  * const end   = s < success_begin ? 0 : m_ruleMap + be::peek<uint16>(o_rule_map);

        if (e.test(begin >= rule_map_end || end > rule_map_end || begin > end, E_BADRULEMAPPING))
        {
            face.error_context((face.error_context() & 0xFFFF00) + EC_ARULEMAP + int(n << 24));
            return face.error(e);
        }
        s->rules = begin;
        s->rules_end = (end - begin <= FiniteStateMachine::MAX_RULES)? end :
            begin + FiniteStateMachine::MAX_RULES;
        if (begin)      // keep UBSan happy can't call qsort with null begin
            qsort(begin, end - begin, sizeof(RuleEntry), &cmpRuleEntry);
    }

    return true;
}

bool Pass::readRanges(const byte * ranges, size_t num_ranges, Error &e)
{
    m_cols = gralloc<uint16>(m_numGlyphs);
    if (e.test(!m_cols, E_OUTOFMEM)) return false;
    memset(m_cols, 0xFF, m_numGlyphs * sizeof(uint16));
    for (size_t n = num_ranges; n; --n)
    {
        uint16     * ci     = m_cols + be::read<uint16>(ranges),
                   * ci_end = m_cols + be::read<uint16>(ranges) + 1,
                     col    = be::read<uint16>(ranges);

        if (e.test(ci >= ci_end || ci_end > m_cols+m_numGlyphs || col >= m_numColumns, E_BADRANGE))
            return false;

        // A glyph must only belong to one column at a time
        while (ci != ci_end && *ci == 0xffff)
            *ci++ = col;

        if (e.test(ci != ci_end, E_BADRANGE))
            return false;
    }
    return true;
}

namespace
{

// Sets of numbers below some n as arrays of bits, for Pass::buildFilter.
inline bool testBit(const uint32 * set, size_t i)   { return (set[i >> 5] >> (i & 31)) & 1; }
inline void setBit(uint32 * set, size_t i)          { set[i >> 5] |= uint32(1) << (i & 31); }

// The first member of the set that is not below i, or n if there is none.
inline size_t nextBit(const uint32 * set, size_t i, const size_t n)
{
    while (i < n)
    {
        const uint32 bits = set[i >> 5] >> (i & 31);
        if (bits & 1) return i;
        i = bits ? i + 1 : (i | 31) + 1;
    }
    return n;
}

// Entries of a transition table that are looked at in one go.
typedef unsigned long long chunk_t;
enum { CHUNK = sizeof(chunk_t) / sizeof(uint16) };

// Calls visit(column, state) for each entry of a row of a transition table
// that is not what the row ref has in the same column, or for each entry
// if there is no ref. The rows of the states a run can be in at one slot are
// mostly alike, so that going through what each has that the one before it
// has not takes far less than going through all of each.
template <typename V>
inline void scanRow(const uint16 * const row, const uint16 * const ref, const size_t n, V & visit)
{
    const uint16 * p = row, * const end = row + n;
    if (!ref)
    {
        for (; p != end; ++p) visit(p - row, *p);
        return;
    }
    const ptrdiff_t d = ref - row;
    for (; end - p >= CHUNK; p += CHUNK)
    {
        chunk_t a, b;
        memcpy(&a, p, sizeof a);
        memcpy(&b, p + d, sizeof b);
        if (a == b) continue;
        for (int i = 0; i != CHUNK; ++i)
            if (p[i] != p[d + i]) visit(p - row + i, p[i]);
    }
    for (; p != end; ++p)
        if (*p != p[d]) visit(p - row, *p);
}

// What a column can do, as bits. At the cursor:
enum { CAN_GO_ON = 1,   // lead to a state that has transitions,
       CAN_MATCH = 2,   // lead to a state that has rules,
       CAN_VARY  = 4,   // lead to one state or another, going by what came before.
       CAN_STOP  = 8 }; // Before the cursor: end the run.

// What m_filter says of a glyph at the cursor.
enum { FILTER_CAN = 1,      // a rule can match
       FILTER_ALONE = 2 };  // and whatever glyph follows

// What m_context says of a glyph, as bits.
enum { CONTEXT_SAFE    = 1,     // before the cursor: the run is sure to go on;
       CONTEXT_UNIFORM = 2 };   // at the cursor: it makes no difference which state the machine comes in.

// Collects the different states that entries of a transition table lead
// to, less state 0, which ends a run, and notes the columns that lead to
// states with no way on.
class Targets
{
public:
    // seen: a zeroed byte per state; list: room for every state.
    Targets(byte * seen, uint16 * list, byte * can, size_t numTrans)
    : m_seen(seen), m_list(list), m_can(can), m_numTrans(numTrans), m_size(0) { if (seen) seen[0] = 1; }

    void operator () (const size_t col, const uint16 state)
    {
        if (state == 0 || state >= m_numTrans) m_can[col] |= CAN_STOP;
        if (m_seen[state]) return;
        m_seen[state] = 1;
        m_list[m_size++] = state;
    }
    // Hands them out, last first.
    bool   empty() const    { return m_size == 0; }
    uint16 pop()            { const uint16 state = m_list[--m_size]; m_seen[state] = 0; return state; }

private:
    byte   * m_seen;
    uint16 * m_list;
    byte   * m_can;
    const size_t m_numTrans;
    size_t   m_size;
};

// Notes what each column can do at the cursor, and each transition state a
// column leads to there.
class Columns
{
public:
    struct Step { uint16 col, state; };

    // can and last: a zeroed entry per column; steps: room for as many as are added before clear().
    Columns(byte * can, uint16 * last, Step * steps, const State * states, size_t successStart, size_t numTrans)
    : m_can(can), m_last(last), m_steps(steps), m_states(states),
      m_successStart(successStart), m_numTrans(numTrans), m_size(0), m_vary(0) {}

    void operator () (const size_t col, const uint16 state)
    {
        m_can[col] |= m_vary;
        if (state >= m_successStart && !m_states[state].empty())
            m_can[col] |= CAN_MATCH;
        if (state == 0 || state >= m_numTrans || state == m_last[col]) return;
        m_can[col] |= CAN_GO_ON;
        m_last[col] = state;
        m_steps[m_size].col = uint16(col);
        m_steps[m_size++].state = state;
    }
    // From now on an entry seen is one that another state does not have.
    void varying()                              { m_vary = CAN_VARY; }
    size_t size() const                         { return m_size; }
    const Step & operator [] (size_t i) const   { return m_steps[i]; }
    void clear()                                { m_size = 0; }

private:
    byte        * m_can;
    uint16      * m_last;
    Step        * m_steps;
    const State * m_states;
    const size_t  m_successStart,
                  m_numTrans;
    size_t        m_size;
    byte          m_vary;
};

} // end of namespace

// Sets up the test couldMatch() makes before the state machine is run at a
// slot: whether, with the glyph at the slot and the one that follows it, the
// run can end with any rule to test at all.
//
// runFSM() starts up to m_maxPreCtxt slots before the cursor and makes one
// transition per slot, and a rule is only there to be tested once a success
// state holding rules has been entered. Whatever glyphs come before the
// cursor, the state the machine is in when it gets to the cursor is one of a
// set that can be read off the table: the start states, followed through all
// their transitions for as many slots as come before the cursor. If none of
// that set gets anywhere with the glyph at the cursor and then with the one
// after it, the run cannot yield a rule.
//
// Anything not provably so is left to runFSM(): the filter only ever says
// that a run would be fruitless, and a pass it cannot be worked out for (a
// table in which rules turn up before the cursor is reached, or where the
// sets take too long to follow) gets none.
//
// The same sets tell runFSM() when it need not work its way to the cursor.
// For most glyphs it makes no difference to the transition at the cursor
// which of the states the machine arrives in (CONTEXT_UNIFORM): no rule that
// could match there minds what came before. If, besides, each of the slots
// before the cursor has a glyph that takes every state the machine can be in
// at that slot to another state with transitions (CONTEXT_SAFE), the run is
// certain to get to the cursor in one of those states, and runFSM() can
// start there in any of them: m_atCursor.
//
// All of this takes the slots to be linked consistently, so that going back
// from the cursor and forward again comes to the cursor.
//
// ranges is what readRanges() has checked and read m_cols from.
bool Pass::buildFilter(const byte * ranges, size_t num_ranges, Face & face, Error &e)
{
    const size_t numTrans = m_numTransition,
                 numCols  = m_numColumns,
                 setWords = (numTrans + 31) >> 5,
    // A row of m_filterPairs is a set of what may come next: bit 0 stands for
    // nothing more being needed, bit c+1 for a glyph of column c.
                 rowWords = (numCols + 32) >> 5,
                 maxSteps = numCols + m_numStates;
    // The rows are no use for a table with next to no states, and must not
    // take more room than the table they are made from.
    const bool   pairs    = 2 * rowWords <= numTrans,
    // Whether there is enough before the cursor for runFSM() to gain by
    // leaving it out, which takes some doing itself, and room in the slot
    // map to do it without counting slots.
                 shortcut = m_maxPreCtxt > 2 && m_maxPreCtxt < SlotMap::MAX_SLOTS - 1;
    const uint16 * const transitions = m_transitions;
    const State  * const states = m_states;
    const uint16 successStart = m_successStart;

    // A transition to state 0 ends a run. Should state 0 hold rules, the
    // run does not end empty handed and no transition can be written off.
    if (numTrans == 0 || (successStart == 0 && !states[0].empty()))
        return true;

    // sets:   two sets of transition states, one before a slot and one after;
    // seen, list: for the different states the rows of one of the sets lead to;
    // can, last, steps: for what the columns lead to, at the cursor and before;
    // next:   for each transition state entered at the cursor, in the order
    //         they turn up, its row as the set of columns it goes on with;
    // nextOf: which of those sets is a state's.
    uint32 * const sets   = grzeroalloc<uint32>(2 * setWords);
    byte   * const seen   = grzeroalloc<byte>(m_numStates);
    uint16 * const list   = gralloc<uint16>(m_numStates);
    byte   * const can    = grzeroalloc<byte>(numCols);
    uint16 * const last   = grzeroalloc<uint16>(numCols);
    Columns::Step * const steps = gralloc<Columns::Step>(maxSteps);
    uint32 * const next   = pairs ? gralloc<uint32>(numTrans * rowWords) : 0;
    uint16 * const nextOf = gralloc<uint16>(numTrans);
    byte   * const filter = grzeroalloc<byte>(m_numGlyphs);
    byte   * const context = shortcut ? grzeroalloc<byte>(m_numGlyphs + numCols) : 0,
           * const before = context ? context + m_numGlyphs : 0;    // the same, per column
    uint32 * const filterPairs = pairs ? grzeroalloc<uint32>(numCols * rowWords) : 0;

    // Rows of the transition table we are prepared to look at; an operation
    // on a row of filterPairs counts for as much of one as it is long.
    size_t budget  = 4 * numTrans + 16,
           merged  = 0,
           numNext = 0;
    bool   usable  = sets && seen && list && can && last && steps && nextOf && filter
                        && (!pairs || (next && filterPairs)) && (!shortcut || context);
    const bool nomem = !usable;

    uint32 * cur = sets, * nxt = sets + setWords;

    // The states the machine can be in at each slot before the cursor.
    Targets targets(seen, list, can, numTrans);
    for (int k = m_maxPreCtxt; usable; --k)
    {
        // A run that has k slots before the cursor starts here.
        if (k >= m_minPreCtxt && m_startStates[m_maxPreCtxt - k] < numTrans)
            setBit(cur, m_startStates[m_maxPreCtxt - k]);
        if (k == 0) break;

        const uint16 * ref = 0;
        for (size_t s = nextBit(cur, 0, numTrans); s != numTrans; s = nextBit(cur, s + 1, numTrans))
        {
            if (budget-- == 0) { usable = false; break; }
            const uint16 * const row = transitions + s * numCols;
            scanRow(row, ref, numCols, targets);
            ref = row;
        }
        memset(nxt, 0, setWords * sizeof(uint32));
        while (!targets.empty())
        {
            const uint16 t = targets.pop();
            // A rule before the cursor is reached: it does not depend on the
            // glyph at the cursor, which is all we will look at.
            if (t >= successStart && !states[t].empty())
                usable = false;
            else if (t < numTrans)
                setBit(nxt, t);
        }
        uint32 * const tmp = cur; cur = nxt; nxt = tmp;
    }

    // What each column leads to at the cursor and, for the columns that
    // need more than themselves, what can follow. nxt now records the
    // states whose rows are in next.
    Columns columns(can, last, steps, states, successStart, numTrans);
    const uint16 * ref = 0;
    size_t s = usable ? nextBit(cur, 0, numTrans) : numTrans;
    const size_t atCursor = s;
    if (usable) memset(nxt, 0, setWords * sizeof(uint32));
    while (usable && (s != numTrans || columns.size()))
    {
        for (; s != numTrans && columns.size() + numCols <= maxSteps; s = nextBit(cur, s + 1, numTrans))
        {
            if (budget-- == 0) { usable = false; break; }
            const uint16 * const row = transitions + s * numCols;
            scanRow(row, ref, numCols, columns);
            columns.varying();
            ref = row;
        }
        for (size_t i = 0; pairs && i != columns.size() && usable; ++i)
        {
            const size_t c = columns[i].col,
                         t = columns[i].state;
            if (can[c] & CAN_MATCH) continue;
            if (!testBit(nxt, t))
            {
                if (budget-- == 0) { usable = false; break; }
                setBit(nxt, t);
                nextOf[t] = uint16(numNext);
                uint32 * const set = next + numNext++ * rowWords;
                memset(set, 0, rowWords * sizeof(uint32));
                const uint16 * const row = transitions + t * numCols;
                size_t d = 0;
                for (; d + CHUNK <= numCols; d += CHUNK)
                {
                    chunk_t some;
                    memcpy(&some, row + d, sizeof some);
                    if (!some) continue;
                    uint32 bits = 0;
                    for (size_t j = 0; j != CHUNK; ++j)
                        bits |= uint32(row[d + j] != 0) << j;
                    const size_t at = d + 1;
                    set[at >> 5] |= bits << (at & 31);
                    if ((at & 31) > 32 - CHUNK)
                        set[(at >> 5) + 1] |= bits >> (32 - (at & 31));
                }
                for (; d != numCols; ++d)
                    if (row[d] != 0) setBit(set, d + 1);
            }
            uint32 * const pair = filterPairs + c * rowWords;
            const uint32 * const set = next + nextOf[t] * rowWords;
            for (size_t j = 0; j != rowWords; ++j)
                pair[j] |= set[j];
            merged += rowWords;
            if (merged >= numCols)
            {
                merged -= numCols;
                if (budget-- == 0) usable = false;
            }
        }
        columns.clear();
    }

    // What m_filter and m_context are to say of the glyphs of each column.
    bool worthwhile = false, pairsWorthwhile = false, contextWorthwhile = false;
    for (size_t c = 0; c != numCols && usable; ++c)
    {
        if (shortcut && atCursor != numTrans)
        {
            if (!(can[c] & CAN_STOP)) before[c] = CONTEXT_SAFE;
            if (!(can[c] & CAN_VARY))
            {
                before[c] |= CONTEXT_UNIFORM;
                contextWorthwhile = true;
            }
        }
        int flags = 0;
        if (can[c] & CAN_MATCH)
        {
            flags = FILTER_CAN | FILTER_ALONE;
            if (pairs) memset(filterPairs + c * rowWords, 0xFF, rowWords * sizeof(uint32));
        }
        else if (can[c] & CAN_GO_ON)
        {
            bool follows = !pairs;
            for (size_t j = 0; j != rowWords && !follows; ++j)
                follows = filterPairs[c * rowWords + j] != 0;
            if (follows) flags = FILTER_CAN;
            pairsWorthwhile |= pairs && follows;
        }
        can[c] = byte(flags);
    }

    if (usable)
    {
        size_t n = 0;
        for (; num_ranges; --num_ranges)
        {
            const size_t first = be::read<uint16>(ranges),
                         end   = be::read<uint16>(ranges) + 1,
                         col   = be::read<uint16>(ranges);
            if (contextWorthwhile && before[col])
                memset(context + first, before[col], end - first);
            if (!can[col]) continue;
            memset(filter + first, can[col], end - first);
            n += end - first;
        }
        worthwhile = n != m_numGlyphs;
    }

    free(sets);
    free(seen);
    free(list);
    free(can);
    free(last);
    free(steps);
    free(next);
    free(nextOf);
    if (usable && pairsWorthwhile)
    {
        m_filterPairs = filterPairs;
        m_filterWords = uint16(rowWords);
    }
    else
        free(filterPairs);
    if (usable && (worthwhile || pairsWorthwhile))
        m_filter = filter;
    else
        free(filter);
    if (usable && contextWorthwhile)
    {
        m_context = context;
        m_atCursor = uint16(atCursor);
    }
    else
        free(context);
    if (e.test(nomem, E_OUTOFMEM)) return face.error(e);
    return true;
}

// False only when runFSM() at this slot is certain to end with no rule to test.
inline
bool Pass::couldMatch(const Slot * slot) const
{
    const byte * const filter = m_filter;
    if (!filter) return true;

    const unsigned int gid = slot->gid();
    if (gid >= m_numGlyphs) return false;
    const unsigned int can = filter[gid];
    if (can != FILTER_CAN) return can != 0;

    const uint32 * pairs = m_filterPairs;
    if (!pairs) return true;

    // Column of the glyph that follows, plus one; 0 if there is none.
    const Slot * const next = slot->next();
    unsigned int follows = 0;
    if (next && next->gid() < m_numGlyphs)
        follows = uint16(m_cols[next->gid()] + 1);
    pairs += m_cols[gid] * m_filterWords;
    return (pairs[follows >> 5] >> (follows & 31)) & 1;
}


bool Pass::runGraphite(vm::Machine & m, FiniteStateMachine & fsm, bool reverse) const
{
    Slot *s = m.slotMap().segment.first();
    if (!s || !testPassConstraint(m)) return true;
    if (reverse)
    {
        m.slotMap().segment.reverseSlots();
        s = m.slotMap().segment.first();
    }
    if (m_numRules)
    {
        Slot *currHigh = s->next();

#if !defined GRAPHITE2_NTRACING
        if (fsm.dbgout)  *fsm.dbgout << "rules" << json::array;
        json::closer rules_array_closer(fsm.dbgout);
#endif

        m.slotMap().highwater(currHigh);
        int lc = m_iMaxLoop;
        bool match = couldMatch(s);
        do
        {
            // Without a rule to test, all findNDoRule does is to move on,
            // and only a rule can change the machine's status.
            if (match)
            {
                findNDoRule(s, m, fsm);
                if (m.status() != Machine::finished) return false;
            }
            else
                s = s->next();
            if (s && (s == m.slotMap().highwater() || m.slotMap().highpassed() || --lc == 0)) {
                if (!lc)
                    s = m.slotMap().highwater();
                lc = m_iMaxLoop;
                if (s)
                {
                    // With the high water mark put after s, as it is about
                    // to be, each slot that nothing can match takes one turn
                    // of this loop that moves s on by one and comes back to
                    // this point. Take those turns here.
                    while (!(match = couldMatch(s)) && s->next())
                        s = s->next();
                    m.slotMap().highwater(s->next());
                    continue;
                }
            }
            if (s) match = couldMatch(s);
        } while (s);
    }
    //TODO: Use enums for flags
    const bool collisions = m_numCollRuns || m_kernColls;

    if (!collisions || !m.slotMap().segment.hasCollisionInfo())
        return true;

    if (m_numCollRuns)
    {
        if (!(m.slotMap().segment.flags() & Segment::SEG_INITCOLLISIONS))
        {
            m.slotMap().segment.positionSlots(0, 0, 0, m.slotMap().dir(), true);
//            m.slotMap().segment.flags(m.slotMap().segment.flags() | Segment::SEG_INITCOLLISIONS);
        }
        if (!collisionShift(&m.slotMap().segment, m.slotMap().dir(), fsm.dbgout))
            return false;
    }
    if ((m_kernColls) && !collisionKern(&m.slotMap().segment, m.slotMap().dir(), fsm.dbgout))
        return false;
    if (collisions && !collisionFinish(&m.slotMap().segment, fsm.dbgout))
        return false;
    return true;
}

// Runs the state machine from slot on, in state, with the slots before it
// already in the map up to free.
inline
bool Pass::runFrom(FiniteStateMachine & fsm, Slot * slot, unsigned int state, Slot * * free) const
{
    // Nothing here changes the tables: read what the loop needs once.
    const uint16 * const cols        = m_cols,
                 * const transitions = m_transitions;
    const State  * const states      = m_states;
    const unsigned int numGlyphs     = m_numGlyphs,
                       numTransition = m_numTransition,
                       numColumns    = m_numColumns,
                       successStart  = m_successStart;
    // The slots go into the map from its start; there is room for MAX_SLOTS.
    Slot * * const map = fsm.slots.begin(),
         * * const end = map + SlotMap::MAX_SLOTS;
    // A state without transitions ends the run once one more slot is in
    // the map. As m_successStart is not above m_numTransition, only a start
    // state or a success state can be one, and never state 0 once in the
    // loop: it is tested for where it can turn up.
    if (state >= numTransition)
        *free++ = slot;
    else for (;;)
    {
        *free++ = slot;
        const unsigned int gid = slot->gid();
        if (gid >= numGlyphs) break;
        const unsigned int col = cols[gid];
        if (col == 0xffffU) break;
        if (free == end)
        {
            fsm.slots.size(SlotMap::MAX_SLOTS);
            return false;
        }

        state = transitions[state*numColumns + col];
        if (state >= successStart)
        {
            fsm.rules.accumulate_rules(states[state]);
            if (state >= numTransition)
            {
                // What the loop would do with the next slot before it
                // came to test the state.
                slot = slot->next();
                *free++ = slot;
                if (slot && slot->gid() < numGlyphs
                        && cols[slot->gid()] != 0xffffU && free == end)
                {
                    fsm.slots.size(SlotMap::MAX_SLOTS);
                    return false;
                }
                break;
            }
        }

        slot = slot->next();
        if (state == 0 || !slot)
        {
            *free++ = slot;
            break;
        }
    }

    fsm.slots.size(free - map);
    return true;
}

// runFSM() for a slot whose glyph has CONTEXT_UNIFORM: buildFilter() has
// found that it leads to the same state from all the states the machine can
// reach the cursor in. If the glyphs before it are ones that are sure to
// take the machine there, the run can start at the cursor, in m_atCursor,
// with the slots before it in the map just as the run through them would
// leave them.
bool Pass::runAtCursor(FiniteStateMachine & fsm, Slot * const cursor) const
{
    // Going back, the slots are put into the map so that the last of them
    // ends where it would if there were m_maxPreCtxt of them, and moved down
    // if there are fewer.
    const byte * const context = m_context;
    const unsigned int numGlyphs = m_numGlyphs;
    Slot * slot = cursor;
    Slot * * const map = fsm.slots.begin(),
         * * const last = map + m_maxPreCtxt,
         * * place = last;
    bool safe = true;
    while (place != map && slot->prev())
    {
        slot = slot->prev();
        *--place = slot;
        const unsigned int gid = slot->gid();
        if (gid >= numGlyphs || !(context[gid] & CONTEXT_SAFE))
            safe = false;
    }
    const unsigned int ctxt = (unsigned int)(last - place);
    if (place != map)
        for (Slot * * to = map; place != last; ) *to++ = *place++;
    fsm.rules.clear();
    fsm.slots.reset(*slot, (unsigned short)(ctxt));
    if (ctxt < m_minPreCtxt)
        return false;
    const unsigned int state = m_startStates[m_maxPreCtxt - ctxt];
    if (safe && state < m_numTransition)
        return runFrom(fsm, cursor, m_atCursor, map + ctxt);
    return runFrom(fsm, slot, state, map);
}

bool Pass::runFSM(FiniteStateMachine& fsm, Slot * slot) const
{
    const byte * const context = m_context;
    if (context && slot->gid() < m_numGlyphs && (context[slot->gid()] & CONTEXT_UNIFORM))
        return runAtCursor(fsm, slot);

    fsm.reset(slot, m_maxPreCtxt);
    if (fsm.slots.context() < m_minPreCtxt)
        return false;
    return runFrom(fsm, slot, m_startStates[m_maxPreCtxt - fsm.slots.context()], fsm.slots.begin());
}

#if !defined GRAPHITE2_NTRACING

inline
Slot * input_slot(const SlotMap &  slots, const int n)
{
    Slot * s = slots[slots.context() + n];
    if (!s->isCopied())     return s;

    return s->prev() ? s->prev()->next() : (s->next() ? s->next()->prev() : slots.segment.last());
}

inline
Slot * output_slot(const SlotMap &  slots, const int n)
{
    Slot * s = slots[slots.context() + n - 1];
    return s ? s->next() : slots.segment.first();
}

#endif //!defined GRAPHITE2_NTRACING

void Pass::findNDoRule(Slot * & slot, Machine &m, FiniteStateMachine & fsm) const
{
    assert(slot);

    if (runFSM(fsm, slot))
    {
        // Search for the first rule which passes the constraint
        const RuleEntry *        r = fsm.rules.begin(),
                        * const re = fsm.rules.end();
        while (r != re && !testConstraint(*r->rule, m))
        {
            ++r;
            if (m.status() != Machine::finished)
                return;
        }

#if !defined GRAPHITE2_NTRACING
        if (fsm.dbgout)
        {
            if (fsm.rules.size() != 0)
            {
                *fsm.dbgout << json::item << json::object;
                dumpRuleEventConsidered(fsm, *r);
                if (r != re)
                {
                    const int adv = doAction(r->rule->action, slot, m);
                    dumpRuleEventOutput(fsm, *r->rule, slot);
                    if (r->rule->action->deletes()) fsm.slots.collectGarbage(slot);
                    adjustSlot(adv, slot, fsm.slots);
                    *fsm.dbgout << "cursor" << objectid(dslot(&fsm.slots.segment, slot))
                            << json::close; // Close RuelEvent object

                    return;
                }
                else
                {
                    *fsm.dbgout << json::close  // close "considered" array
                            << "output" << json::null
                            << "cursor" << objectid(dslot(&fsm.slots.segment, slot->next()))
                            << json::close;
                }
            }
        }
        else
#endif
        {
            if (r != re)
            {
                const int adv = doAction(r->rule->action, slot, m);
                if (m.status() != Machine::finished) return;
                if (r->rule->action->deletes()) fsm.slots.collectGarbage(slot);
                adjustSlot(adv, slot, fsm.slots);
                return;
            }
        }
    }

    slot = slot->next();
    return;
}

#if !defined GRAPHITE2_NTRACING

void Pass::dumpRuleEventConsidered(const FiniteStateMachine & fsm, const RuleEntry & re) const
{
    *fsm.dbgout << "considered" << json::array;
    for (const RuleEntry *r = fsm.rules.begin(); r != &re; ++r)
    {
        if (r->rule->preContext > fsm.slots.context())
            continue;
        *fsm.dbgout << json::flat << json::object
                    << "id" << r->rule - m_rules
                    << "failed" << true
                    << "input" << json::flat << json::object
                        << "start" << objectid(dslot(&fsm.slots.segment, input_slot(fsm.slots, -r->rule->preContext)))
                        << "length" << r->rule->sort
                        << json::close  // close "input"
                    << json::close; // close Rule object
    }
}


void Pass::dumpRuleEventOutput(const FiniteStateMachine & fsm, const Rule & r, Slot * const last_slot) const
{
    *fsm.dbgout     << json::item << json::flat << json::object
                        << "id"     << &r - m_rules
                        << "failed" << false
                        << "input" << json::flat << json::object
                            << "start" << objectid(dslot(&fsm.slots.segment, input_slot(fsm.slots, 0)))
                            << "length" << r.sort - r.preContext
                            << json::close // close "input"
                        << json::close  // close Rule object
                << json::close // close considered array
                << "output" << json::object
                    << "range" << json::flat << json::object
                        << "start"  << objectid(dslot(&fsm.slots.segment, input_slot(fsm.slots, 0)))
                        << "end"    << objectid(dslot(&fsm.slots.segment, last_slot))
                    << json::close // close "input"
                    << "slots"  << json::array;
    const Position rsb_prepos = last_slot ? last_slot->origin() : fsm.slots.segment.advance();
    fsm.slots.segment.positionSlots(0, 0, 0, fsm.slots.segment.currdir());

    for(Slot * slot = output_slot(fsm.slots, 0); slot != last_slot; slot = slot->next())
        *fsm.dbgout     << dslot(&fsm.slots.segment, slot);
    *fsm.dbgout         << json::close  // close "slots"
                    << "postshift"  << (last_slot ? last_slot->origin() : fsm.slots.segment.advance()) - rsb_prepos
                << json::close;         // close "output" object

}

#endif


inline
bool Pass::testPassConstraint(Machine & m) const
{
    if (!m_cPConstraint) return true;

    assert(m_cPConstraint.constraint());

    m.slotMap().reset(*m.slotMap().segment.first(), 0);
    m.slotMap().pushSlot(m.slotMap().segment.first());
    vm::slotref * map = m.slotMap().begin();
    const uint32 ret = m_cPConstraint.run(m, map);

#if !defined GRAPHITE2_NTRACING
    json * const dbgout = m.slotMap().segment.getFace()->logger();
    if (dbgout)
        *dbgout << "constraint" << (ret && m.status() == Machine::finished);
#endif

    return ret && m.status() == Machine::finished;
}


bool Pass::testConstraint(const Rule & r, Machine & m) const
{
    const uint16 curr_context = m.slotMap().context();
    if (unsigned(r.sort + curr_context - r.preContext) > m.slotMap().size()
        || curr_context - r.preContext < 0) return false;

    vm::slotref * map = m.slotMap().begin() + curr_context - r.preContext;
    if (map[r.sort - 1] == 0)
        return false;

    if (!*r.constraint) return true;
    assert(r.constraint->constraint());
    // A constraint cannot change the slot map, so whether the slots it refers
    // to are there is the same for every slot it is run on. At least one is:
    // the last was tested above.
    if (!r.constraint->haveSlots(m)) return false;
    for (int n = r.sort; n && map; --n, ++map)
    {
        if (!*map) continue;
        const int32 ret = r.constraint->exec(m, map);
        if (!ret || m.status() != Machine::finished)
            return false;
    }

    return true;
}


void FiniteStateMachine::Rules::merge(const State &state)
{
  // Merge the new sorted rules list into the current sorted result set.
  const RuleEntry * lre = begin(), * rre = state.rules;
  RuleEntry * out = m_rules + (m_begin == m_rules)*MAX_RULES;
  const RuleEntry * const lrend = out + MAX_RULES,
                  * const rrend = state.rules_end;
  m_begin = out;
  while (lre != end() && out != lrend)
  {
    if (*lre < *rre)      *out++ = *lre++;
    else if (*rre < *lre) { *out++ = *rre++; }
    else                { *out++ = *lre++; ++rre; }

    if (rre == rrend)
    {
      while (lre != end() && out != lrend) { *out++ = *lre++; }
      m_end = out;
      return;
    }
  }
  while (rre != rrend && out != lrend) { *out++ = *rre++; }
  m_end = out;
}


void SlotMap::collectGarbage(Slot * &aSlot)
{
    for(Slot **s = begin(), *const *const se = end() - 1; s != se; ++s) {
        Slot *& slot = *s;
        if(slot && (slot->isDeleted() || slot->isCopied()))
        {
            if (slot == aSlot)
                aSlot = slot->prev() ? slot->prev() : slot->next();
            segment.freeSlot(slot);
        }
    }
}



inline
int Pass::doAction(const Code *codeptr, Slot * & slot_out, vm::Machine & m) const
{
    assert(codeptr);
    if (!*codeptr) return 0;
    SlotMap   & smap = m.slotMap();
    vm::slotref * map = &smap[smap.context()];
    smap.highpassed(false);

    int32 ret = 1;
    if (codeptr->haveSlots(m))
        ret = codeptr->simple() ? codeptr->runSimple(m, map) : codeptr->exec(m, map);

    if (m.status() != Machine::finished)
    {
        slot_out = NULL;
        smap.highwater(0);
        return 0;
    }

    slot_out = *map;
    return ret;
}


void Pass::adjustSlot(int delta, Slot * & slot_out, SlotMap & smap) const
{
    if (!slot_out)
    {
        if (smap.highpassed() || slot_out == smap.highwater())
        {
            slot_out = smap.segment.last();
            ++delta;
            if (!smap.highwater() || smap.highwater() == slot_out)
                smap.highpassed(false);
        }
        else
        {
            slot_out = smap.segment.first();
            --delta;
        }
    }
    if (delta < 0)
    {
        while (++delta <= 0 && slot_out)
        {
            slot_out = slot_out->prev();
            if (smap.highpassed() && smap.highwater() == slot_out)
                smap.highpassed(false);
        }
    }
    else if (delta > 0)
    {
        while (--delta >= 0 && slot_out)
        {
            if (slot_out == smap.highwater() && slot_out)
                smap.highpassed(true);
            slot_out = slot_out->next();
        }
    }
}

bool Pass::collisionShift(Segment *seg, int dir, json * const dbgout) const
{
    ShiftCollider shiftcoll(dbgout);
    // bool isfirst = true;
    bool hasCollisions = false;
    Slot *start = seg->first();      // turn on collision fixing for the first slot
    Slot *end = NULL;
    bool moved = false;

#if !defined GRAPHITE2_NTRACING
    if (dbgout)
        *dbgout << "collisions" << json::array
            << json::flat << json::object << "num-loops" << m_numCollRuns << json::close;
#endif

    while (start)
    {
#if !defined GRAPHITE2_NTRACING
        if (dbgout)  *dbgout << json::object << "phase" << "1" << "moves" << json::array;
#endif
        hasCollisions = false;
        end = NULL;
        // phase 1 : position shiftable glyphs, ignoring kernable glyphs
        for (Slot *s = start; s; s = s->next())
        {
            const SlotCollision * c = seg->collisionInfo(s);
            if (start && (c->flags() & (SlotCollision::COLL_FIX | SlotCollision::COLL_KERN)) == SlotCollision::COLL_FIX
                      && !resolveCollisions(seg, s, start, shiftcoll, false, dir, moved, hasCollisions, dbgout))
                return false;
            if (s != start && (c->flags() & SlotCollision::COLL_END))
            {
                end = s->next();
                break;
            }
        }

#if !defined GRAPHITE2_NTRACING
        if (dbgout)
            *dbgout << json::close << json::close; // phase-1
#endif

        // phase 2 : loop until happy.
        for (int i = 0; i < m_numCollRuns - 1; ++i)
        {
            if (hasCollisions || moved)
            {

#if !defined GRAPHITE2_NTRACING
                if (dbgout)
                    *dbgout << json::object << "phase" << "2a" << "loop" << i << "moves" << json::array;
#endif
                // phase 2a : if any shiftable glyphs are in collision, iterate backwards,
                // fixing them and ignoring other non-collided glyphs. Note that this handles ONLY
                // glyphs that are actually in collision from phases 1 or 2b, and working backwards
                // has the intended effect of breaking logjams.
                if (hasCollisions)
                {
                    hasCollisions = false;
                    #if 0
                    moved = true;
                    for (Slot *s = start; s != end; s = s->next())
                    {
                        SlotCollision * c = seg->collisionInfo(s);
                        c->setShift(Position(0, 0));
                    }
                    #endif
                    Slot *lend = end ? end->prev() : seg->last();
                    Slot *lstart = start->prev();
                    for (Slot *s = lend; s != lstart; s = s->prev())
                    {
                        SlotCollision * c = seg->collisionInfo(s);
                        if (start && (c->flags() & (SlotCollision::COLL_FIX | SlotCollision::COLL_KERN | SlotCollision::COLL_ISCOL))
                                        == (SlotCollision::COLL_FIX | SlotCollision::COLL_ISCOL)) // ONLY if this glyph is still colliding
                        {
                            if (!resolveCollisions(seg, s, lend, shiftcoll, true, dir, moved, hasCollisions, dbgout))
                                return false;
                            c->setFlags(c->flags() | SlotCollision::COLL_TEMPLOCK);
                        }
                    }
                }

#if !defined GRAPHITE2_NTRACING
                if (dbgout)
                    *dbgout << json::close << json::close // phase 2a
                        << json::object << "phase" << "2b" << "loop" << i << "moves" << json::array;
#endif

                // phase 2b : redo basic diacritic positioning pass for ALL glyphs. Each successive loop adjusts
                // glyphs from their current adjusted position, which has the effect of gradually minimizing the
                // resulting adjustment; ie, the final result will be gradually closer to the original location.
                // Also it allows more flexibility in the final adjustment, since it is moving along the
                // possible 8 vectors from successively different starting locations.
                if (moved)
                {
                    moved = false;
                    for (Slot *s = start; s != end; s = s->next())
                    {
                        SlotCollision * c = seg->collisionInfo(s);
                        if (start && (c->flags() & (SlotCollision::COLL_FIX | SlotCollision::COLL_TEMPLOCK
                                                        | SlotCollision::COLL_KERN)) == SlotCollision::COLL_FIX
                                  && !resolveCollisions(seg, s, start, shiftcoll, false, dir, moved, hasCollisions, dbgout))
                            return false;
                        else if (c->flags() & SlotCollision::COLL_TEMPLOCK)
                            c->setFlags(c->flags() & ~SlotCollision::COLL_TEMPLOCK);
                    }
                }
        //      if (!hasCollisions) // no, don't leave yet because phase 2b will continue to improve things
        //          break;
#if !defined GRAPHITE2_NTRACING
                if (dbgout)
                    *dbgout << json::close << json::close; // phase 2
#endif
            }
        }
        if (!end)
            break;
        start = NULL;
        for (Slot *s = end->prev(); s; s = s->next())
        {
            if (seg->collisionInfo(s)->flags() & SlotCollision::COLL_START)
            {
                start = s;
                break;
            }
        }
    }
    return true;
}

bool Pass::collisionKern(Segment *seg, int dir, json * const dbgout) const
{
    Slot *start = seg->first();
    float ymin = 1e38f;
    float ymax = -1e38f;
    const GlyphCache &gc = seg->getFace()->glyphs();
    KernCollider coll(dbgout);      // one for all the slots, so that its memory is reused

    // phase 3 : handle kerning of clusters
#if !defined GRAPHITE2_NTRACING
    if (dbgout)
        *dbgout << json::object << "phase" << "3" << "moves" << json::array;
#endif

    for (Slot *s = seg->first(); s; s = s->next())
    {
        if (!gc.check(s->gid()))
            return false;
        const SlotCollision * c = seg->collisionInfo(s);
        const Rect &bbox = seg->theGlyphBBoxTemporary(s->gid());
        float y = s->origin().y + c->shift().y;
        if (!(c->flags() & SlotCollision::COLL_ISSPACE))
        {
            ymax = max(y + bbox.tr.y, ymax);
            ymin = min(y + bbox.bl.y, ymin);
        }
        if (start && (c->flags() & (SlotCollision::COLL_KERN | SlotCollision::COLL_FIX))
                        == (SlotCollision::COLL_KERN | SlotCollision::COLL_FIX))
            resolveKern(seg, s, start, coll, dir, ymin, ymax, dbgout);
        if (c->flags() & SlotCollision::COLL_END)
            start = NULL;
        if (c->flags() & SlotCollision::COLL_START)
            start = s;
    }

#if !defined GRAPHITE2_NTRACING
    if (dbgout)
        *dbgout << json::close << json::close; // phase 3
#endif
    return true;
}

bool Pass::collisionFinish(Segment *seg, GR_MAYBE_UNUSED json * const dbgout) const
{
    for (Slot *s = seg->first(); s; s = s->next())
    {
        SlotCollision *c = seg->collisionInfo(s);
        if (c->shift().x != 0 || c->shift().y != 0)
        {
            const Position newOffset = c->shift();
            const Position nullPosition(0, 0);
            c->setOffset(newOffset + c->offset());
            c->setShift(nullPosition);
        }
    }
//    seg->positionSlots();

#if !defined GRAPHITE2_NTRACING
        if (dbgout)
            *dbgout << json::close;
#endif
    return true;
}

// Can slot s be kerned, or is it attached to something that can be kerned?
static bool inKernCluster(Segment *seg, Slot *s)
{
    SlotCollision *c = seg->collisionInfo(s);
    if (c->flags() & SlotCollision::COLL_KERN /** && c->flags() & SlotCollision::COLL_FIX **/ )
        return true;
    while (s->attachedTo())
    {
        s = s->attachedTo();
        c = seg->collisionInfo(s);
        if (c->flags() & SlotCollision::COLL_KERN /** && c->flags() & SlotCollision::COLL_FIX **/ )
            return true;
    }
    return false;
}

// Fix collisions for the given slot.
// Return true if everything was fixed, false if there are still collisions remaining.
// isRev means be we are processing backwards.
bool Pass::resolveCollisions(Segment *seg, Slot *slotFix, Slot *start,
        ShiftCollider &coll, GR_MAYBE_UNUSED bool isRev, int dir, bool &moved, bool &hasCol,
        json * const dbgout) const
{
    Slot * nbor;  // neighboring slot
    SlotCollision *cFix = seg->collisionInfo(slotFix);
    if (!coll.initSlot(seg, slotFix, cFix->limit(), cFix->margin(), cFix->marginWt(),
            cFix->shift(), cFix->offset(), dir, dbgout))
        return false;
    bool collides = false;
    // When we're processing forward, ignore kernable glyphs that preceed the target glyph.
    // When processing backward, don't ignore these until we pass slotFix.
    bool ignoreForKern = !isRev;
    bool rtl = dir & 1;
    Slot *base = slotFix;
    while (base->attachedTo())
        base = base->attachedTo();
    Position zero(0., 0.);

    // Look for collisions with the neighboring glyphs.
    for (nbor = start; nbor; nbor = isRev ? nbor->prev() : nbor->next())
    {
        SlotCollision *cNbor = seg->collisionInfo(nbor);
        bool sameCluster = nbor->isChildOf(base);
        if (nbor != slotFix         						// don't process if this is the slot of interest
                      && !(cNbor->ignore())    				// don't process if ignoring
                      && (nbor == base || sameCluster       // process if in the same cluster as slotFix
                            || !inKernCluster(seg, nbor))   // or this cluster is not to be kerned
//                            || (rtl ^ ignoreForKern))       // or it comes before(ltr) or after(rtl)
                      && (!isRev    // if processing forwards then good to merge otherwise only:
                            || !(cNbor->flags() & SlotCollision::COLL_FIX)     // merge in immovable stuff
                            || ((cNbor->flags() & SlotCollision::COLL_KERN) && !sameCluster)     // ignore other kernable clusters
                            || (cNbor->flags() & SlotCollision::COLL_ISCOL))   // test against other collided glyphs
                      && !coll.mergeSlot(seg, nbor, cNbor, cNbor->shift(), !ignoreForKern, sameCluster, collides, false, dbgout))
            return false;
        else if (nbor == slotFix)
            // Switching sides of this glyph - if we were ignoring kernable stuff before, don't anymore.
            ignoreForKern = !ignoreForKern;

        if (nbor != start && (cNbor->flags() & (isRev ? SlotCollision::COLL_START : SlotCollision::COLL_END)))
            break;
    }
    bool isCol = false;
    if (collides || cFix->shift().x != 0.f || cFix->shift().y != 0.f)
    {
        Position shift = coll.resolve(seg, isCol, dbgout);
        // isCol has been set to true if a collision remains.
        if (std::fabs(shift.x) < 1e38f && std::fabs(shift.y) < 1e38f)
        {
            if (sqr(shift.x-cFix->shift().x) + sqr(shift.y-cFix->shift().y) >= m_colThreshold * m_colThreshold)
                moved = true;
            cFix->setShift(shift);
            if (slotFix->firstChild())
            {
                Rect bbox;
                Position here = slotFix->origin() + shift;
                float clusterMin = here.x;
                slotFix->firstChild()->finalise(seg, NULL, here, bbox, 0, clusterMin, rtl, false);
            }
        }
    }
    else
    {
        // This glyph is not colliding with anything.
#if !defined GRAPHITE2_NTRACING
        if (dbgout)
        {
            *dbgout << json::object
                            << "missed" << objectid(dslot(seg, slotFix));
            coll.outputJsonDbg(dbgout, seg, -1);
            *dbgout << json::close;
        }
#endif
    }

    // Set the is-collision flag bit.
    if (isCol)
    { cFix->setFlags(cFix->flags() | SlotCollision::COLL_ISCOL | SlotCollision::COLL_KNOWN); }
    else
    { cFix->setFlags((cFix->flags() & ~SlotCollision::COLL_ISCOL) | SlotCollision::COLL_KNOWN); }
    hasCol |= isCol;
    return true;
}

float Pass::resolveKern(Segment *seg, Slot *slotFix, GR_MAYBE_UNUSED Slot *start, KernCollider &coll, int dir,
    float &ymin, float &ymax, json *const dbgout) const
{
    Slot *nbor; // neighboring slot
    float currSpace = 0.;
    bool collides = false;
    unsigned int space_count = 0;
    Slot *base = slotFix;
    while (base->attachedTo())
        base = base->attachedTo();
    SlotCollision *cFix = seg->collisionInfo(base);
    const GlyphCache &gc = seg->getFace()->glyphs();
    const Rect &bbb = seg->theGlyphBBoxTemporary(slotFix->gid());
    const float by = slotFix->origin().y + cFix->shift().y;

    if (base != slotFix)
    {
        cFix->setFlags(cFix->flags() | SlotCollision::COLL_KERN | SlotCollision::COLL_FIX);
        return 0;
    }
    bool seenEnd = (cFix->flags() & SlotCollision::COLL_END) != 0;
    bool isInit = false;
    coll.reset();

    ymax = max(by + bbb.tr.y, ymax);
    ymin = min(by + bbb.bl.y, ymin);
    for (nbor = slotFix->next(); nbor; nbor = nbor->next())
    {
        if (!gc.check(nbor->gid()))
            return 0.;
        const Rect &bb = seg->theGlyphBBoxTemporary(nbor->gid());
        SlotCollision *cNbor = seg->collisionInfo(nbor);
        const float nby = nbor->origin().y + cNbor->shift().y;
        if (nbor->isChildOf(base))
        {
            ymax = max(nby + bb.tr.y, ymax);
            ymin = min(nby + bb.bl.y, ymin);
            continue;
        }
        if ((bb.bl.y == 0.f && bb.tr.y == 0.f) || (cNbor->flags() & SlotCollision::COLL_ISSPACE))
        {
            if (m_kernColls == InWord)
                break;
            // Add space for a space glyph.
            currSpace += nbor->advance();
            ++space_count;
        }
        else
        {
            space_count = 0;
            if (nbor != slotFix && !cNbor->ignore())
            {
                seenEnd = true;
                if (!isInit)
                {
                    if (!coll.initSlot(seg, slotFix, cFix->limit(), cFix->margin(),
                                    cFix->shift(), cFix->offset(), dir, ymin, ymax, dbgout))
                        return 0.;
                    isInit = true;
                }
                collides |= coll.mergeSlot(seg, nbor, cNbor->shift(), currSpace, dir, dbgout);
            }
        }
        if (cNbor->flags() & SlotCollision::COLL_END)
        {
            if (seenEnd && space_count < 2)
                break;
            else
                seenEnd = true;
        }
    }
    if (collides)
    {
        Position mv = coll.resolve(seg, slotFix, dir, dbgout);
        Position delta = slotFix->advancePos() + mv - cFix->shift();
        slotFix->advance(delta);
        cFix->setShift(mv);
        return mv.x;
    }
    return 0.;
}
