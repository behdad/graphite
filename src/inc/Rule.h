// SPDX-License-Identifier: MIT OR MPL-2.0 OR LGPL-2.1-or-later OR GPL-2.0-or-later
// Copyright 2011, SIL International, All rights reserved.


#pragma once

#include "inc/Code.h"
#include "inc/Slot.h"

namespace graphite2 {

struct Rule {
  const vm::Machine::Code * constraint,
                 * action;
  unsigned short   sort;
  byte             preContext;
#ifndef NDEBUG
  uint16           rule_idx;
#endif

  Rule();
  ~Rule() {}

  CLASS_NEW_DELETE;

private:
  Rule(const Rule &);
  Rule & operator = (const Rule &);
};

inline
Rule::Rule()
: constraint(0),
  action(0),
  sort(0),
  preContext(0)
{
#ifndef NDEBUG
  rule_idx = 0;
#endif
}


struct RuleEntry
{
  const Rule   * rule;

  inline
  bool operator < (const RuleEntry &r) const
  {
    const unsigned short lsort = rule->sort, rsort = r.rule->sort;
    return lsort > rsort || (lsort == rsort && rule < r.rule);
  }

  inline
  bool operator == (const RuleEntry &r) const
  {
    return rule == r.rule;
  }
};


struct State
{
  const RuleEntry     * rules,
                      * rules_end;

  bool   empty() const;
};

inline
bool State::empty() const
{
    return rules_end == rules;
}


class SlotMap
{
public:
  enum {MAX_SLOTS=64};
  SlotMap(Segment & seg, uint8 direction, size_t maxSize);

  Slot       * * begin();
  Slot       * * end();
  size_t         size() const;
  void           size(size_t n);
  unsigned short context() const;
  void           reset(Slot &, unsigned short);

  Slot * const & operator[](int n) const;
  Slot       * & operator [] (int);
  void           pushSlot(Slot * const slot);
  void           collectGarbage(Slot *& aSlot);

  Slot         * highwater() { return m_highwater; }
  void           highwater(Slot *s) { m_highwater = s; m_highpassed = false; }
  bool           highpassed() const { return m_highpassed; }
  void           highpassed(bool v) { m_highpassed = v; }

  uint8          dir() const { return m_dir; }
  int            decMax() { return --m_maxSize; }

  Segment &    segment;
private:
  Slot         * m_slot_map[MAX_SLOTS+1];
  unsigned short m_size;
  unsigned short m_precontext;
  Slot         * m_highwater;
  int            m_maxSize;
  uint8          m_dir;
  bool           m_highpassed;
};


class FiniteStateMachine
{
public:
  enum {MAX_RULES=128};

private:
  class Rules
  {
  public:
      Rules();
      void              clear();
      const RuleEntry * begin() const;
      const RuleEntry * end() const;
      size_t            size() const;

      void accumulate_rules(const State &state);

  private:
      void merge(const State &state);

      const RuleEntry * m_begin,
                      * m_end;
      RuleEntry         m_rules[MAX_RULES*2];
  };

public:
  FiniteStateMachine(SlotMap & map, json * logger);
  void      reset(Slot * & slot, const short unsigned int max_pre_ctxt);

  Rules     rules;
  SlotMap   & slots;
  json    * const dbgout;
};


inline
FiniteStateMachine::FiniteStateMachine(SlotMap& map, json * logger)
: slots(map),
  dbgout(logger)
{
}

inline
void FiniteStateMachine::reset(Slot * & slot, const short unsigned int max_pre_ctxt)
{
  rules.clear();
  int ctxt = 0;
  for (; ctxt != max_pre_ctxt && slot->prev(); ++ctxt, slot = slot->prev());
  slots.reset(*slot, ctxt);
}

inline
FiniteStateMachine::Rules::Rules()
  : m_begin(m_rules), m_end(m_rules)
{
}

inline
void FiniteStateMachine::Rules::clear()
{
  m_end = m_begin;
}

inline
const RuleEntry * FiniteStateMachine::Rules::begin() const
{
  return m_begin;
}

inline
const RuleEntry * FiniteStateMachine::Rules::end() const
{
  return m_end;
}

inline
size_t FiniteStateMachine::Rules::size() const
{
  return m_end - m_begin;
}

inline
void FiniteStateMachine::Rules::accumulate_rules(const State &state)
{
  // Only bother if there are rules in the State object.
  if (state.empty()) return;

  // The first rules found are used where they are: merged with nothing
  // they would be copied as they are, and a State has at most MAX_RULES.
  if (m_begin == m_end)
  {
    m_begin = state.rules;
    m_end   = state.rules_end;
    return;
  }

  merge(state);
}

inline
SlotMap::SlotMap(Segment & seg, uint8 direction, size_t maxSize)
: segment(seg), m_size(0), m_precontext(0), m_highwater(0),
    m_maxSize(int(maxSize)), m_dir(direction), m_highpassed(false)
{
    m_slot_map[0] = 0;
}

inline
Slot * * SlotMap::begin()
{
  return &m_slot_map[1]; // allow map to go 1 before slot_map when inserting
                         // at start of segment.
}

inline
Slot * * SlotMap::end()
{
  return m_slot_map + m_size + 1;
}

inline
size_t SlotMap::size() const
{
  return m_size;
}

inline
void SlotMap::size(size_t n)
{
  m_size = (unsigned short)(n);
}

inline
short unsigned int SlotMap::context() const
{
  return m_precontext;
}

inline
void SlotMap::reset(Slot & slot, short unsigned int ctxt)
{
  m_size = 0;
  m_precontext = ctxt;
  *m_slot_map = slot.prev();
}

inline
void SlotMap::pushSlot(Slot*const slot)
{
  m_slot_map[++m_size] = slot;
}

inline
Slot * const & SlotMap::operator[](int n) const
{
  return m_slot_map[n + 1];
}

inline
Slot * & SlotMap::operator[](int n)
{
  return m_slot_map[n + 1];
}

// The parts of running a program that need the slot map.
inline
bool vm::Machine::Code::haveSlots(vm::Machine & m) const
{
    const SlotMap & smap = m.slotMap();
    if (smap.size() <= size_t(_max_ref + smap.context())
        || smap[_max_ref + smap.context()] == 0)
    {
        m._status = Machine::slot_offset_out_bounds;
        return false;
    }
    return true;
}

inline
int32 vm::Machine::Code::run(vm::Machine & m, vm::slotref * & map) const
{
    return haveSlots(m) ? exec(m, map) : 1;
}

// Runs a simple() action after haveSlots(), without the virtual machine: this
// does, in the same order, what the instructions of such a program do (see
// Code::find_setters and opcodes.h). The program refers to no slot but the
// one it is started at, which haveSlots() has found to be there, and so to be
// followed in the slot map by at least the entry that NEXT moves to. All its
// values go through the first stack entry and leave the stack empty.
// The machine's slotat() refuses a slot offset that leads outside the slot
// map. The only offset in such a program is 0, from the entry the program is
// started at (nothing in it moves from there before NEXT), and haveSlots()
// has found that entry to be inside the map: there is nothing to refuse.
inline
int32 vm::Machine::Code::runSimple(vm::Machine & m, vm::slotref * & map) const
{
    SlotMap           & smap = m.slotMap();
    Segment            & seg = smap.segment;
    assert(map >= smap.begin() && map < smap.end());
    const vm::slotref     is = *map;
    const byte          * dp = _data;

    // put_copy 0 is asked to copy the slot onto itself: it copies nothing.
    if (_simple & PUT_COPY_0)
    {
        ++dp;
        if (!is->isDeleted())
        {
            is->markCopied(false);
            is->markDeleted(false);
        }
    }

    for (unsigned n = _simple >> SETTERS_SHIFT, kinds = _setters; n; --n, kinds >>= 2)
    {
        attrCode    slat;
        uint8       idx = 0;
        int         val;
        switch (kinds & 3)
        {
        case BYTE_ATTR :        // push_byte, attr_set
            val  = int8(dp[0]);
            slat = attrCode(uint8(dp[1]));
            dp  += 2;
            break;
        case SHORT_ATTR :       // push_short, attr_set
        {
            const int16 r   = int16(dp[0]) << 8
                            | uint8(dp[1]);
            val  = r;
            slat = attrCode(uint8(dp[2]));
            dp  += 3;
            break;
        }
        case BYTE_IATTR :       // push_byte, iattr_set
            val  = int8(dp[0]);
            slat = attrCode(uint8(dp[1]));
            idx  = uint8(dp[2]);
            dp  += 3;
            break;
        default :               // push_slot_attr of this slot, setbits, attr_set
        {
            const int res   = is->getAttr(&seg, attrCode(uint8(dp[0])), 0);
            const uint16 msk = uint16(dp[2]) << 8
                             | uint8(dp[3]);
            const uint16 v   = uint16(dp[4]) << 8
                             | uint8(dp[5]);
            val  = (res & ~msk) | v;
            slat = attrCode(uint8(dp[6]));
            dp  += 7;
            break;
        }
        }
        is->setAttr(&seg, slat, idx, val, smap);
    }

    // next, and what the machine does when a program ends: the slot it has
    // reached is written to the slot map entry it has reached.
    if (is == smap.highwater())
        smap.highpassed(true);
    *++map = is->next();
    // ret_zero
    return 0;
}

} // namespace graphite2
