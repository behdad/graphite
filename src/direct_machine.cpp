// SPDX-License-Identifier: MIT OR MPL-2.0 OR LGPL-2.1-or-later OR GPL-2.0-or-later
// Copyright 2010, SIL International, All rights reserved.

// This direct threaded interpreter implmentation for machine.h
// Author: Tim Eves

// Build either this interpreter or the call_machine implementation.
// The direct threaded interpreter is relies upon a gcc feature called
// labels-as-values so is only portable to compilers that support the
// extension (gcc only as far as I know) however it should build on any
// architecture gcc supports.
// This is twice as fast as the call threaded model and is likely faster on
// inorder processors with short pipelines and little branch prediction such
// as the ARM and possibly Atom chips.


#include <cassert>
#include <cstring>
#include "inc/Machine.h"
#include "inc/Segment.h"
#include "inc/Slot.h"
#include "inc/Rule.h"

#define STARTOP(name)           name: {
#define ENDOP                   }; goto *((sp - sb)/Machine::STACK_MAX ? &&end : *++ip);
#define ENDOP_SAME              }; goto **++ip;
#define ENDOP_PUSH              }; goto *(sp >= sl ? &&end : *++ip);
#define ENDOP_POP               }; goto *(sp < sb ? &&end : *++ip);
#define EXIT(status)            { push(status); goto end; }

#define do_(name)               &&name

// Two of the registers opcodes.h expects are read where they are used: few
// programs use them, and neither can change while a program runs.
#define mapb                    (smap.begin()+smap.context())
#define dir                     smap.dir()


using namespace graphite2;
using namespace vm;

namespace {

// The GCC manual has this to say about labels as values:
//   The &&foo expressions for the same label might have different values
//   if the containing function is inlined or cloned. If a program relies
//   on them being always the same, __attribute__((__noinline__,__noclone__))
//   should be used to prevent inlining and cloning.
//
// is_return in Code.cpp relies on being able to do comparisons, so it needs
// them to be always the same.
//
// The GCC manual further adds:
//   If &&foo is used in a static variable initializer, inlining and
//   cloning is forbidden.
//
// In this file, &&foo *is* used in a static variable initializer, and it's not
// entirely clear whether this should prevent inlining of the function or not.
// In practice, though, clang 7 can end up inlining the function with ThinLTO,
// which breaks at least is_return. https://bugs.llvm.org/show_bug.cgi?id=39241
// So all in all, we need at least the __noinline__ attribute. __noclone__
// is not supported by clang.
__attribute__((__noinline__))
Machine::stack_t direct_run(SlotMap           * __smap,
                            const instr       * program,
                            const byte        * data,
                            slotref         * & __map,
                            Machine::stack_t  * stack,
                            Machine::status_t & status)
{
    // We need to define and return to opcode table from within this function
    // other inorder to take the addresses of the instruction bodies.
    #include "inc/opcode_table.h"
    // Called without a program this only hands out the opcode table: stack
    // is then where the caller wants its address.
    if (!program)
    {
        const opcode_t * const table = opcode_table;
        memcpy(stack, &table, sizeof table);
        return 0;
    }

    // Declare virtual machine registers
    const instr           * ip = program;
    const byte            * dp = data;
    Machine::stack_t      * sp = stack + Machine::STACK_GUARD,
                    * const sb = sp,
                    * const sl = sb + Machine::STACK_MAX;
    SlotMap             & smap = *__smap;
    Segment              & seg = smap.segment;
    slotref                 is = *__map,
                         * map = __map;
    int8                 flags = 0;

    // start the program
    goto **ip;

    // Pull in the opcode definitions
    #include "inc/opcodes.h"

    end:
    __map  = map;
    *__map = is;

    // The value the program returns is the one value it leaves on the stack.
    // Anything else on the stack is an error, unless the program has already
    // reported one. (Machine::check_final_stack says the same.)
    const Machine::stack_t ret = sp == sb + 1 ? *sp-- : 0;
    if (status == Machine::finished && sp != sb)
        status = sp <  sb ? Machine::stack_underflow
               : sp >= sl ? Machine::stack_overflow
                          : Machine::stack_not_empty;
    return ret;
}

}

const opcode_t * Machine::getOpcodeTable() throw()
{
    const opcode_t * table;
    slotref * dummy;
    Machine::status_t dumstat;
    direct_run(0, 0, 0, dummy, reinterpret_cast<Machine::stack_t *>(&table), dumstat);
    return table;
}


Machine::stack_t  Machine::run(const instr   * program,
                               const byte    * data,
                               slotref     * & is)
{
    assert(program != 0);

    return direct_run(&_map, program, data, is, _stack, _status);
}
