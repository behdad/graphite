// SPDX-License-Identifier: MIT OR MPL-2.0 OR LGPL-2.1-or-later OR GPL-2.0-or-later
// Copyright 2010, SIL International, All rights reserved.

#pragma once
// This file will be pulled into and integrated into a machine implmentation
// DO NOT build directly and under no circumstances ever #include headers in
// here or you will break the direct_machine.
//
// Implementers' notes
// ==================
// You have access to a few primitives and the full C++ code:
//    declare_params(n) Tells the interpreter how many bytes of parameter
//                      space to claim for this instruction uses and
//                      initialises the param pointer.  You *must* before the
//                      first use of param.
//    use_params(n)     Claim n extra bytes of param space beyond what was
//                      claimed using delcare_param.
//    param             A const byte pointer for the parameter space claimed by
//                      this instruction.
//    binop(op)         Implement a binary operation on the stack using the
//                      specified C++ operator.
//    NOT_IMPLEMENTED   Any instruction body containing this will exit the
//                      program with an assertion error.  Instructions that are
//                      not implemented should also be marked NILOP in the
//                      opcodes tables this will cause the code class to spot
//                      them in a live code stream and throw a runtime_error
//                      instead.
//    push(n)           Push the value n onto the stack.
//    pop()             Pop the top most value and return it.
//
//    Every instruction body ends with one of four terminators. They all stop
//    the program when the stack pointer has left the stack, that is unless
//    0 <= sp - sb < STACK_MAX, which holds when an instruction starts. They
//    differ in how much of that an instruction can have broken:
//    ENDOP             Tests both bounds.
//    ENDOP_SAME        For an instruction that leaves sp where it was: there
//                      is nothing to test.
//    ENDOP_PUSH        For an instruction that pushes at most one value more
//                      than it pops: only the upper bound needs testing.
//    ENDOP_POP         For an instruction that never leaves sp higher than
//                      it found it: only the lower bound needs testing.
//
//    FALLBACK(name)    In a fused instruction, which stands in the place of
//                      the first of a run of instructions and does the work
//                      of them all: leave it to that first instruction, name,
//                      after all. Nothing may have been changed before, the
//                      registers included, except by slotat(): the status it
//                      sets for a slot offset outside the slot map is set
//                      again by name's own slotat().
//
//    You have access to the following named fast 'registers':
//        sp        = The pointer to the current top of stack, the last value
//                    pushed.
//        seg       = A reference to the Segment this code is running over.
//        is        = The current slot index
//        isb       = The original base slot index at the start of this rule
//        isf       = The first positioned slot
//        isl       = The last positioned slot
//        ip        = The current instruction pointer
//        endPos    = Position of advance of last cluster
//        dir       = writing system directionality of the font


// #define NOT_IMPLEMENTED     assert(false)
// #define NOT_IMPLEMENTED

#define binop(op)           const uint32 a = pop(); *sp = uint32(*sp) op a
#define sbinop(op)          const int32 a = pop(); *sp = int32(*sp) op a
#define use_params(n)       dp += n

#define declare_params(n)   const byte * param = dp; \
                            use_params(n);

#define push(n)             { *++sp = n; }
#define pop()               (*sp--)
#define slotat(x)           ((map + (x) >= &smap[-1] && map + (x) < smap.end()) ? \
                                map[(x)] : (status = Machine::slot_offset_out_bounds, nullptr))
#define DIE                 { is=seg.last(); status = Machine::died_early; EXIT(1); }
#define POSITIONED          1

STARTOP(nop)
    do {} while (0);
ENDOP_SAME

STARTOP(push_byte)
    declare_params(1);
    push(int8(*param));
ENDOP_PUSH

STARTOP(push_byte_u)
    declare_params(1);
    push(uint8(*param));
ENDOP_PUSH

STARTOP(push_short)
    declare_params(2);
    const int16 r   = int16(param[0]) << 8
                    | uint8(param[1]);
    push(r);
ENDOP_PUSH

STARTOP(push_short_u)
    declare_params(2);
    const uint16 r  = uint16(param[0]) << 8
                    | uint8(param[1]);
    push(r);
ENDOP_PUSH

STARTOP(push_long)
    declare_params(4);
    const  int32 r  = int32(param[0]) << 24
                    | uint32(param[1]) << 16
                    | uint32(param[2]) << 8
                    | uint8(param[3]);
    push(r);
ENDOP_PUSH

STARTOP(add)
    binop(+);
ENDOP_POP

STARTOP(sub)
    binop(-);
ENDOP_POP

STARTOP(mul)
    binop(*);
ENDOP_POP

STARTOP(div_)
    const int32 b = pop();
    const int32 a = int32(*sp);
    if (b == 0 || (a == std::numeric_limits<int32>::min() && b == -1)) DIE;
    *sp = int32(*sp) / b;
ENDOP_POP

STARTOP(min_)
    const int32 a = pop(), b = *sp;
    if (a < b) *sp = a;
ENDOP_POP

STARTOP(max_)
    const int32 a = pop(), b = *sp;
    if (a > b) *sp = a;
ENDOP_POP

STARTOP(neg)
    *sp = uint32(-int32(*sp));
ENDOP_SAME

STARTOP(trunc8)
    *sp = uint8(*sp);
ENDOP_SAME

STARTOP(trunc16)
    *sp = uint16(*sp);
ENDOP_SAME

STARTOP(cond)
    const uint32 f = pop(), t = pop(), c = pop();
    push(c ? t : f);
ENDOP_POP

STARTOP(and_)
    binop(&&);
ENDOP_POP

STARTOP(or_)
    binop(||);
ENDOP_POP

STARTOP(not_)
    *sp = !*sp;
ENDOP_SAME

STARTOP(equal)
    binop(==);
ENDOP_POP

STARTOP(not_eq_)
    binop(!=);
ENDOP_POP

STARTOP(less)
    sbinop(<);
ENDOP_POP

STARTOP(gtr)
    sbinop(>);
ENDOP_POP

STARTOP(less_eq)
    sbinop(<=);
ENDOP_POP

STARTOP(gtr_eq)
    sbinop(>=);
ENDOP_POP

STARTOP(next)
    if (map - &smap[0] >= int(smap.size())) DIE
    if (is)
    {
        if (is == smap.highwater())
            smap.highpassed(true);
        is = is->next();
    }
    ++map;
ENDOP_SAME

//STARTOP(next_n)
//    use_params(1);
//    NOT_IMPLEMENTED;
    //declare_params(1);
    //const size_t num = uint8(*param);
//ENDOP

//STARTOP(copy_next)
//     if (is) is = is->next();
//     ++map;
// ENDOP

STARTOP(put_glyph_8bit_obs)
    declare_params(1);
    const unsigned int output_class = uint8(*param);
    is->setGlyph(&seg, seg.getClassGlyph(output_class, 0));
ENDOP_SAME

STARTOP(put_subs_8bit_obs)
    declare_params(3);
    const int           slot_ref     = int8(param[0]);
    const unsigned int  input_class  = uint8(param[1]),
                        output_class = uint8(param[2]);
    uint16 index;
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        index = seg.findClassIndex(input_class, slot->gid());
        is->setGlyph(&seg, seg.getClassGlyph(output_class, index));
    }
ENDOP_SAME

STARTOP(put_copy)
    declare_params(1);
    const int  slot_ref = int8(*param);
    if (is && !is->isDeleted())
    {
        slotref ref = slotat(slot_ref);
        if (ref && ref != is)
        {
            int16 *tempUserAttrs = is->userAttrs();
            if (is->attachedTo() || is->firstChild()) DIE
            Slot *prev = is->prev();
            Slot *next = is->next();
            memcpy(tempUserAttrs, ref->userAttrs(), seg.numAttrs() * sizeof(uint16));
            memcpy(is, ref, sizeof(Slot));
            is->firstChild(NULL);
            is->nextSibling(NULL);
            is->userAttrs(tempUserAttrs);
            is->next(next);
            is->prev(prev);
            if (is->attachedTo())
                is->attachedTo()->child(is);
        }
        is->markCopied(false);
        is->markDeleted(false);
    }
ENDOP_SAME

STARTOP(insert)
    if (smap.decMax() <= 0) DIE;
    Slot *newSlot = seg.newSlot();
    if (!newSlot) DIE;
    Slot *iss = is;
    while (iss && iss->isDeleted()) iss = iss->next();
    if (!iss)
    {
        if (seg.last())
        {
            seg.last()->next(newSlot);
            newSlot->prev(seg.last());
            newSlot->before(seg.last()->before());
            seg.last(newSlot);
        }
        else
        {
            seg.first(newSlot);
            seg.last(newSlot);
        }
    }
    else if (iss->prev())
    {
        iss->prev()->next(newSlot);
        newSlot->prev(iss->prev());
        newSlot->before(iss->prev()->after());
    }
    else
    {
        newSlot->prev(NULL);
        newSlot->before(iss->before());
        seg.first(newSlot);
    }
    newSlot->next(iss);
    if (iss)
    {
        iss->prev(newSlot);
        newSlot->originate(iss->original());
        newSlot->after(iss->before());
    }
    else if (newSlot->prev())
    {
        newSlot->originate(newSlot->prev()->original());
        newSlot->after(newSlot->prev()->after());
    }
    else
    {
        newSlot->originate(seg.defaultOriginal());
    }
    if (is == smap.highwater())
        smap.highpassed(false);
    is = newSlot;
    seg.extendLength(1);
    if (map != &smap[-1])
        --map;
ENDOP_SAME

STARTOP(delete_)
    if (!is || is->isDeleted()) DIE
    is->markDeleted(true);
    if (is->prev())
        is->prev()->next(is->next());
    else
        seg.first(is->next());

    if (is->next())
        is->next()->prev(is->prev());
    else
        seg.last(is->prev());


    if (is == smap.highwater())
            smap.highwater(is->next());
    if (is->prev())
        is = is->prev();
    seg.extendLength(-1);
ENDOP_SAME

STARTOP(assoc)
    declare_params(1);
    unsigned int  num = uint8(*param);
    const int8 *  assocs = reinterpret_cast<const int8 *>(param+1);
    use_params(num);
    int max = -1;
    int min = -1;

    while (num-- > 0)
    {
        int sr = *assocs++;
        slotref ts = slotat(sr);
        if (ts && (min == -1 || ts->before() < min)) min = ts->before();
        if (ts && ts->after() > max) max = ts->after();
    }
    if (min > -1)   // implies max > -1
    {
        is->before(min);
        is->after(max);
    }
ENDOP_SAME

STARTOP(cntxt_item)
    // It turns out this is a cunningly disguised condition forward jump.
    declare_params(3);
    const int       is_arg = int8(param[0]);
    const size_t    iskip  = uint8(param[1]),
                    dskip  = uint8(param[2]);

    if (mapb + is_arg != map)
    {
        ip += iskip;
        dp += dskip;
        push(true);
    }
ENDOP_PUSH

STARTOP(attr_set)
    declare_params(1);
    const attrCode      slat = attrCode(uint8(*param));
    const          int  val  = pop();
    is->setAttr(&seg, slat, 0, val, smap);
ENDOP_POP

STARTOP(attr_add)
    declare_params(1);
    const attrCode      slat = attrCode(uint8(*param));
    const     uint32_t  val  = pop();
    if ((slat == gr_slatPosX || slat == gr_slatPosY) && (flags & POSITIONED) == 0)
    {
        seg.positionSlots(0, *smap.begin(), *(smap.end()-1), seg.currdir());
        flags |= POSITIONED;
    }
    uint32_t res = uint32_t(is->getAttr(&seg, slat, 0));
    is->setAttr(&seg, slat, 0, int32_t(val + res), smap);
ENDOP_POP

STARTOP(attr_sub)
    declare_params(1);
    const attrCode      slat = attrCode(uint8(*param));
    const     uint32_t  val  = pop();
    if ((slat == gr_slatPosX || slat == gr_slatPosY) && (flags & POSITIONED) == 0)
    {
        seg.positionSlots(0, *smap.begin(), *(smap.end()-1), seg.currdir());
        flags |= POSITIONED;
    }
    uint32_t res = uint32_t(is->getAttr(&seg, slat, 0));
    is->setAttr(&seg, slat, 0, int32_t(res - val), smap);
ENDOP_POP

STARTOP(attr_set_slot)
    declare_params(1);
    const attrCode  slat   = attrCode(uint8(*param));
    const int       offset = int(map - smap.begin())*int(slat == gr_slatAttTo);
    const int       val    = pop()  + offset;
    is->setAttr(&seg, slat, offset, val, smap);
ENDOP_POP

STARTOP(iattr_set_slot)
    declare_params(2);
    const attrCode  slat = attrCode(uint8(param[0]));
    const uint8     idx  = uint8(param[1]);
    const int       val  = int(pop()  + (map - smap.begin())*int(slat == gr_slatAttTo));
    is->setAttr(&seg, slat, idx, val, smap);
ENDOP_POP

STARTOP(push_slot_attr)
    declare_params(2);
    const attrCode      slat     = attrCode(uint8(param[0]));
    const int           slot_ref = int8(param[1]);
    if ((slat == gr_slatPosX || slat == gr_slatPosY) && (flags & POSITIONED) == 0)
    {
        seg.positionSlots(0, *smap.begin(), *(smap.end()-1), seg.currdir());
        flags |= POSITIONED;
    }
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        int res = slot->getAttr(&seg, slat, 0);
        push(res);
    }
ENDOP_PUSH

STARTOP(push_glyph_attr_obs)
    declare_params(2);
    const unsigned int  glyph_attr = uint8(param[0]);
    const int           slot_ref   = int8(param[1]);
    slotref slot = slotat(slot_ref);
    if (slot)
        push(int32(seg.glyphAttr(slot->gid(), glyph_attr)));
ENDOP_PUSH

STARTOP(push_glyph_metric)
    declare_params(3);
    const unsigned int  glyph_attr  = uint8(param[0]);
    const int           slot_ref    = int8(param[1]);
    const signed int    attr_level  = uint8(param[2]);
    slotref slot = slotat(slot_ref);
    if (slot)
        push(seg.getGlyphMetric(slot, glyph_attr, attr_level, dir));
ENDOP_PUSH

STARTOP(push_feat)
    declare_params(2);
    const unsigned int  feat        = uint8(param[0]);
    const int           slot_ref    = int8(param[1]);
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        uint8 fid = seg.charinfo(slot->original())->fid();
        push(seg.getFeature(fid, feat));
    }
ENDOP_PUSH

STARTOP(push_att_to_gattr_obs)
    declare_params(2);
    const unsigned int  glyph_attr  = uint8(param[0]);
    const int           slot_ref    = int8(param[1]);
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        slotref att = slot->attachedTo();
        if (att) slot = att;
        push(int32(seg.glyphAttr(slot->gid(), glyph_attr)));
    }
ENDOP_PUSH

STARTOP(push_att_to_glyph_metric)
    declare_params(3);
    const unsigned int  glyph_attr  = uint8(param[0]);
    const int           slot_ref    = int8(param[1]);
    const signed int    attr_level  = uint8(param[2]);
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        slotref att = slot->attachedTo();
        if (att) slot = att;
        push(int32(seg.getGlyphMetric(slot, glyph_attr, attr_level, dir)));
    }
ENDOP_PUSH

STARTOP(push_islot_attr)
    declare_params(3);
    const attrCode  slat     = attrCode(uint8(param[0]));
    const int           slot_ref = int8(param[1]),
                        idx      = uint8(param[2]);
    if ((slat == gr_slatPosX || slat == gr_slatPosY) && (flags & POSITIONED) == 0)
    {
        seg.positionSlots(0, *smap.begin(), *(smap.end()-1), seg.currdir());
        flags |= POSITIONED;
    }
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        int res = slot->getAttr(&seg, slat, idx);
        push(res);
    }
ENDOP_PUSH

#if 0
STARTOP(push_iglyph_attr) // not implemented
    NOT_IMPLEMENTED;
ENDOP
#endif

STARTOP(pop_ret)
    const uint32 ret = pop();
    EXIT(ret);
ENDOP

STARTOP(ret_zero)
    EXIT(0);
ENDOP

STARTOP(ret_true)
    EXIT(1);
ENDOP

STARTOP(iattr_set)
    declare_params(2);
    const attrCode      slat = attrCode(uint8(param[0]));
    const uint8         idx  = uint8(param[1]);
    const          int  val  = pop();
    is->setAttr(&seg, slat, idx, val, smap);
ENDOP_POP

STARTOP(iattr_add)
    declare_params(2);
    const attrCode      slat = attrCode(uint8(param[0]));
    const uint8         idx  = uint8(param[1]);
    const     uint32_t  val  = pop();
    if ((slat == gr_slatPosX || slat == gr_slatPosY) && (flags & POSITIONED) == 0)
    {
        seg.positionSlots(0, *smap.begin(), *(smap.end()-1), seg.currdir());
        flags |= POSITIONED;
    }
    uint32_t res = uint32_t(is->getAttr(&seg, slat, idx));
    is->setAttr(&seg, slat, idx, int32_t(val + res), smap);
ENDOP_POP

STARTOP(iattr_sub)
    declare_params(2);
    const attrCode      slat = attrCode(uint8(param[0]));
    const uint8         idx  = uint8(param[1]);
    const     uint32_t  val  = pop();
    if ((slat == gr_slatPosX || slat == gr_slatPosY) && (flags & POSITIONED) == 0)
    {
        seg.positionSlots(0, *smap.begin(), *(smap.end()-1), seg.currdir());
        flags |= POSITIONED;
    }
    uint32_t res = uint32_t(is->getAttr(&seg, slat, idx));
    is->setAttr(&seg, slat, idx, int32_t(res - val), smap);
ENDOP_POP

STARTOP(push_proc_state)
    use_params(1);
    push(1);
ENDOP_PUSH

STARTOP(push_version)
    push(0x00030000);
ENDOP_PUSH

STARTOP(put_subs)
    declare_params(5);
    const int        slot_ref     = int8(param[0]);
    const unsigned int  input_class  = uint8(param[1]) << 8
                                     | uint8(param[2]);
    const unsigned int  output_class = uint8(param[3]) << 8
                                     | uint8(param[4]);
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        int index = seg.findClassIndex(input_class, slot->gid());
        is->setGlyph(&seg, seg.getClassGlyph(output_class, index));
    }
ENDOP_SAME

#if 0
STARTOP(put_subs2) // not implemented
    NOT_IMPLEMENTED;
ENDOP

STARTOP(put_subs3) // not implemented
    NOT_IMPLEMENTED;
ENDOP
#endif

STARTOP(put_glyph)
    declare_params(2);
    const unsigned int output_class  = uint8(param[0]) << 8
                                     | uint8(param[1]);
    is->setGlyph(&seg, seg.getClassGlyph(output_class, 0));
ENDOP_SAME

STARTOP(push_glyph_attr)
    declare_params(3);
    const unsigned int  glyph_attr  = uint8(param[0]) << 8
                                    | uint8(param[1]);
    const int           slot_ref    = int8(param[2]);
    slotref slot = slotat(slot_ref);
    if (slot)
        push(int32(seg.glyphAttr(slot->gid(), glyph_attr)));
ENDOP_PUSH

STARTOP(push_att_to_glyph_attr)
    declare_params(3);
    const unsigned int  glyph_attr  = uint8(param[0]) << 8
                                    | uint8(param[1]);
    const int           slot_ref    = int8(param[2]);
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        slotref att = slot->attachedTo();
        if (att) slot = att;
        push(int32(seg.glyphAttr(slot->gid(), glyph_attr)));
    }
ENDOP_PUSH

STARTOP(temp_copy)
    slotref newSlot = seg.newSlot();
    if (!newSlot || !is) DIE;
    int16 *tempUserAttrs = newSlot->userAttrs();
    memcpy(newSlot, is, sizeof(Slot));
    memcpy(tempUserAttrs, is->userAttrs(), seg.numAttrs() * sizeof(uint16));
    newSlot->userAttrs(tempUserAttrs);
    newSlot->markCopied(true);
    *map = newSlot;
ENDOP_SAME

STARTOP(band)
    binop(&);
ENDOP_POP

STARTOP(bor)
    binop(|);
ENDOP_POP

STARTOP(bnot)
    *sp = ~*sp;
ENDOP_SAME

STARTOP(setbits)
    declare_params(4);
    const uint16 m  = uint16(param[0]) << 8
                    | uint8(param[1]);
    const uint16 v  = uint16(param[2]) << 8
                    | uint8(param[3]);
    *sp = ((*sp) & ~m) | v;
ENDOP_SAME

STARTOP(set_feat)
    declare_params(2);
    const unsigned int  feat        = uint8(param[0]);
    const int           slot_ref    = int8(param[1]);
    slotref slot = slotat(slot_ref);
    if (slot)
    {
        uint8 fid = seg.charinfo(slot->original())->fid();
        seg.setFeature(fid, feat, pop());
    }
ENDOP_POP

// Fused instructions. None of these comes from a font: Code::fuse puts each
// in the place of the first instruction of a run that the font's code holds.
// It does what the instructions of the run do, in their order, and steps over
// the others, which stay where they are (so that a context item's skip which
// lands on one of them finds it). What it leaves out is the pushing of a
// value that the next instruction of the run pops, and the test of the stack
// bounds between them: the store is to an entry above the stack pointer,
// which nothing reads before it is written again, and Code::fuse makes sure
// the stack cannot overflow. Where the run only works as a whole if a slot is
// there to push a value for, the fused instruction falls back when it is not:
// when the slot map's entry is null, and when slotat() refuses the offset as
// outside the slot map. In both cases the plain instruction then pushes
// nothing and the rest of the run works on what the stack held, as without
// fusing. Every slot offset here goes through slotat().

STARTOP(push_byte_attr_set)
    declare_params(2);
    const          int  val  = int8(param[0]);
    const attrCode      slat = attrCode(uint8(param[1]));
    is->setAttr(&seg, slat, 0, val, smap);
    ++ip;
ENDOP_SAME

STARTOP(push_short_attr_set)
    declare_params(3);
    const int16 r   = int16(param[0]) << 8
                    | uint8(param[1]);
    const          int  val  = r;
    const attrCode      slat = attrCode(uint8(param[2]));
    is->setAttr(&seg, slat, 0, val, smap);
    ++ip;
ENDOP_SAME

STARTOP(push_byte_iattr_set)
    declare_params(3);
    const          int  val  = int8(param[0]);
    const attrCode      slat = attrCode(uint8(param[1]));
    const uint8         idx  = uint8(param[2]);
    is->setAttr(&seg, slat, idx, val, smap);
    ++ip;
ENDOP_SAME

STARTOP(push_glyph_attr_attr_set)
    const byte * param = dp;
    const unsigned int  glyph_attr  = uint8(param[0]) << 8
                                    | uint8(param[1]);
    const int           slot_ref    = int8(param[2]);
    slotref slot = slotat(slot_ref);
    if (!slot) FALLBACK(push_glyph_attr);
    use_params(4);
    const          int  val  = int32(seg.glyphAttr(slot->gid(), glyph_attr));
    const attrCode      slat = attrCode(uint8(param[3]));
    is->setAttr(&seg, slat, 0, val, smap);
    ++ip;
ENDOP_SAME

STARTOP(push_att_to_glyph_attr_attr_set)
    const byte * param = dp;
    const unsigned int  glyph_attr  = uint8(param[0]) << 8
                                    | uint8(param[1]);
    const int           slot_ref    = int8(param[2]);
    slotref slot = slotat(slot_ref);
    if (!slot) FALLBACK(push_att_to_glyph_attr);
    use_params(4);
    slotref att = slot->attachedTo();
    if (att) slot = att;
    const          int  val  = int32(seg.glyphAttr(slot->gid(), glyph_attr));
    const attrCode      slat = attrCode(uint8(param[3]));
    is->setAttr(&seg, slat, 0, val, smap);
    ++ip;
ENDOP_SAME

STARTOP(push_slot_attr_bitset_attr_set)
    const byte * param = dp;
    const attrCode      slat     = attrCode(uint8(param[0]));
    const int           slot_ref = int8(param[1]);
    slotref slot = slotat(slot_ref);
    if (!slot) FALLBACK(push_slot_attr);
    use_params(7);
    if ((slat == gr_slatPosX || slat == gr_slatPosY) && (flags & POSITIONED) == 0)
    {
        seg.positionSlots(0, *smap.begin(), *(smap.end()-1), seg.currdir());
        flags |= POSITIONED;
    }
    const int res = slot->getAttr(&seg, slat, 0);
    const uint16 m  = uint16(param[2]) << 8
                    | uint8(param[3]);
    const uint16 v  = uint16(param[4]) << 8
                    | uint8(param[5]);
    const          int  val  = (res & ~m) | v;
    const attrCode      slat2 = attrCode(uint8(param[6]));
    is->setAttr(&seg, slat2, 0, val, smap);
    ip += 2;
ENDOP_SAME

STARTOP(next_ret_zero)
    if (map - &smap[0] >= int(smap.size())) DIE
    if (is)
    {
        if (is == smap.highwater())
            smap.highpassed(true);
        is = is->next();
    }
    ++map;
    EXIT(0);
ENDOP

STARTOP(next_push_byte_pop_ret)
    if (map - &smap[0] >= int(smap.size())) DIE
    if (is)
    {
        if (is == smap.highwater())
            smap.highpassed(true);
        is = is->next();
    }
    ++map;
    declare_params(1);
    EXIT(int8(*param));
ENDOP
