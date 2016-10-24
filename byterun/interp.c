/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#define _DEFAULT_SOURCE

/* The bytecode interpreter */
#include <stdarg.h>
#include <stdio.h>
#include <sys/mman.h>
#include "caml/alloc.h"
#include "caml/backtrace.h"
#include "caml/callback.h"
#include "caml/debugger.h"
#include "caml/fail.h"
#include "caml/fix_code.h"
#include "caml/instrtrace.h"
#include "caml/instruct.h"
#include "caml/interp.h"
#include "caml/major_gc.h"
#include "caml/memory.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/prims.h"
#include "caml/signals.h"
#include "caml/stacks.h"
#include "caml/startup_aux.h"

#if (defined(THREADED_CODE) && defined(DUMP_JIT_OPCODES)) || (defined(CAML_METHOD_CACHE) && defined(CAML_TEST_CACHE))
/* printf on stderr */
int stderrprintf(const char *fmt, ...) {
  va_list arg;
  int done;

  va_start(arg, fmt);
  done = vfprintf(stderr, fmt, arg);
  va_end(arg);

  return done;
}
#endif

/* Redefinition of macros */
/* Declared in memory.h */
#if defined(NATIVE_CODE) && defined(WITH_SPACETIME)
extern uintnat caml_spacetime_my_profinfo(struct ext_table**, uintnat);
#define _F_Alloc_small(result, wosize, tag) \
  _F_Alloc_small_with_profinfo(result, wosize, tag, \
    _F_caml_spacetime_my_profinfo(NULL, wosize))
#else
#define _F_Alloc_small(result, wosize, tag) \
  _F_Alloc_small_with_profinfo(result, wosize, tag, (uintnat) 0)
#endif
#define _F_Alloc_small_with_profinfo(result, wosize, tag, profinfo) do {       \
                                                CAMLassert ((wosize) >= 1); \
                                          CAMLassert ((tag_t) (tag) < 256); \
                                 CAMLassert ((wosize) <= Max_young_wosize); \
  *_P_caml_young_ptr -= Whsize_wosize (wosize);                                 \
  if (*_P_caml_young_ptr < *_P_caml_young_trigger){                                 \
	  *_P_caml_young_ptr += Whsize_wosize (wosize);                               \
    CAML_INSTR_INT ("force_minor/alloc_small@", 1);                         \
    Setup_for_gc;                                                           \
    _F_caml_gc_dispatch ();                                                    \
    Restore_after_gc;                                                       \
    *_P_caml_young_ptr -= Whsize_wosize (wosize);                               \
  }                                                                         \
  Hd_hp (*_P_caml_young_ptr) =                                                  \
    Make_header_with_profinfo ((wosize), (tag), Caml_black, profinfo);      \
  (result) = Val_hp (*_P_caml_young_ptr);                                       \
  DEBUG_clear ((result), (wosize));                                         \
}while(0)
/* declared in prims.h */
#define _F_Primitive(n) ((c_primitive)(_P_caml_prim_table->contents[n]))
/* declared in mlvalues.h */
#define _F_Atom(tag) (Val_hp (&((*_P_caml_atom_table) [(tag)])))


/* Registers for the abstract machine:
        pc         the code pointer
        sp         the stack pointer (grows downward)
        accu       the accumulator
        env        heap-allocated environment
        caml_trapsp pointer to the current trap frame
        extra_args number of extra arguments provided by the caller

sp is a local copy of the global variable caml_extern_sp. */

/* Instruction decoding */

#ifdef THREADED_CODE
#  define Instruct(name) lbl_##name
#  define InstructEnd(name) lbl_end_##name
/* Next:         from interpreted to interpreted
 * JitNext:      from interpreted/compiled to compiled
 * BreakoutNext: from compiled to interpreted (currently missing)
 * DebugNext:    from compiled to interpreted, in the case of EVENT and BREAK bytecodes
 */
#  if defined(ARCH_SIXTYFOUR) && !defined(ARCH_CODE32)
#    define Jumptbl_base ((char *) &&lbl_ACC0)
#  else
#    define Jumptbl_base ((char *) 0)
#    define jumptbl_base ((char *) 0)
#  endif
#  ifdef DEBUG
#    define Next goto next_instr
#  else
#    define Next goto *(void *)(jumptbl_base + *pc)
#  endif
#define JitNext   __asm__ volatile("jmp *%0" : : "r" (_tgt_table[pc - prog]), "r" (_tgt_table), "r" (pc), "r" (prog))
#define DebugNext __asm__ volatile("jmp *%0" : : "r" (_jumptable[(*_P_caml_saved_code)[pc - *_P_caml_start_code]]), "r" (_jumptable), "r" (_P_caml_saved_code), "r" (pc), "r" (_P_caml_start_code))
#else
#  define Instruct(name) case name
#  define Next break
#  define InstructEnd(name)
#endif

/* GC interface */

#define Setup_for_gc \
  { sp -= 2; sp[0] = accu; sp[1] = env; *_P_caml_extern_sp = sp; }
#define Restore_after_gc \
  { accu = sp[0]; env = sp[1]; sp += 2; }
#define Setup_for_c_call \
  { saved_pc = pc; *--sp = env; *_P_caml_extern_sp = sp; }
#define Restore_after_c_call \
  { sp = *_P_caml_extern_sp; env = *sp++; saved_pc = NULL; }

/* An event frame must look like accu + a C_CALL frame + a RETURN 1 frame */
#define Setup_for_event \
  { sp -= 6; \
    sp[0] = accu; /* accu */ \
    sp[1] = Val_unit; /* C_CALL frame: dummy environment */ \
    sp[2] = Val_unit; /* RETURN frame: dummy local 0 */ \
    sp[3] = (value) pc; /* RETURN frame: saved return address */ \
    sp[4] = env; /* RETURN frame: saved environment */ \
    sp[5] = Val_long(extra_args); /* RETURN frame: saved extra args */ \
    *_P_caml_extern_sp = sp; }
#define Restore_after_event \
  { sp = *_P_caml_extern_sp; accu = sp[0]; \
    pc = (code_t) sp[3]; env = sp[4]; extra_args = Long_val(sp[5]); \
    sp += 6; }

/* Debugger interface */

#define Setup_for_debugger \
   { sp -= 4; \
     sp[0] = accu; sp[1] = (value)(pc - 1); \
     sp[2] = env; sp[3] = Val_long(extra_args); \
     *_P_caml_extern_sp = sp; }
#define Restore_after_debugger { sp += 4; }

#ifdef THREADED_CODE
#define Restart_curr_instr \
  { --pc; goto *(_jumptable[(*_P_caml_saved_code)[pc - *_P_caml_start_code]]); }
#else
#define Restart_curr_instr \
  --pc; \
  curr_instr = caml_saved_code[pc - caml_start_code]; \
  goto dispatch_instr
#endif

/* Register optimization.
   Some compilers underestimate the use of the local variables representing
   the abstract machine registers, and don't put them in hardware registers,
   which slows down the interpreter considerably.
   For GCC, I have hand-assigned hardware registers for several architectures.
*/

#if defined(__GNUC__) && !defined(DEBUG) && !defined(__INTEL_COMPILER) \
    && !defined(__llvm__)
#ifdef __mips__
#define PC_REG asm("$16")
#define SP_REG asm("$17")
#define ACCU_REG asm("$18")
#endif
#ifdef __sparc__
#define PC_REG asm("%l0")
#define SP_REG asm("%l1")
#define ACCU_REG asm("%l2")
#endif
#ifdef __alpha__
#ifdef __CRAY__
#define PC_REG asm("r9")
#define SP_REG asm("r10")
#define ACCU_REG asm("r11")
#define JUMPTBL_BASE_REG asm("r12")
#else
#define PC_REG asm("$9")
#define SP_REG asm("$10")
#define ACCU_REG asm("$11")
#define JUMPTBL_BASE_REG asm("$12")
#endif
#endif
#ifdef __i386__
#define PC_REG asm("%esi")
#define SP_REG asm("%edi")
#define ACCU_REG
#endif
#if defined(__ppc__) || defined(__ppc64__)
#define PC_REG asm("26")
#define SP_REG asm("27")
#define ACCU_REG asm("28")
#endif
#ifdef __hppa__
#define PC_REG asm("%r18")
#define SP_REG asm("%r17")
#define ACCU_REG asm("%r16")
#endif
#ifdef __mc68000__
#define PC_REG asm("a5")
#define SP_REG asm("a4")
#define ACCU_REG asm("d7")
#endif
/* PR#4953: these specific registers not available in Thumb mode */
#if defined (__arm__) && !defined(__thumb__)
#define PC_REG asm("r6")
#define SP_REG asm("r8")
#define ACCU_REG asm("r7")
#endif
#ifdef __ia64__
#define PC_REG asm("36")
#define SP_REG asm("37")
#define ACCU_REG asm("38")
#define JUMPTBL_BASE_REG asm("39")
#endif
#ifdef __x86_64__
#define PC_REG asm("%r15")
#define SP_REG asm("%r14")
#define ACCU_REG asm("%r13")
#endif
#ifdef __aarch64__
#define PC_REG asm("%x19")
#define SP_REG asm("%x20")
#define ACCU_REG asm("%x21")
#define JUMPTBL_BASE_REG asm("%x22")
#endif
#endif

#ifdef DEBUG
static intnat caml_bcodcount;
#endif

#ifdef THREADED_CODE
/* Variables for the jit compiler */
/* These are set by fix_code.c/startup.c */
code_t jit_saved_code;
asize_t jit_saved_code_len;
/* These are local*/
/* Various pointers to code templates */
static void * *codetmpl_entry;
static void * *codetmpl_exit;
static void *check_stacks_entry;
static void *check_stacks_exit;
static void *process_signal_entry;
static void *process_signal_exit;
static void *perform_return_entry;
static void *perform_return_exit;
static void *trampoline_internal_entry;
static void *trampoline_internal_exit;
static void *POPTRAP_trampoline_entry;
static void *POPTRAP_trampoline_exit;
static void *RAISE_trampoline_entry;
static void *RAISE_trampoline_exit;
static void *dbg_trampoline_entry;
static void *dbg_trampoline_exit;
#ifdef DUMP_JIT_OPCODES
static void *echo_entry;
static void *echo_exit;
#endif
static long max_template_size;

/* Target table */
static void* *tgt_table;

/* The compiled binary code (useless, may be used in future to free memory) */
static void *binary = 0;

#ifdef DUMP_JIT_OPCODES
char *mnemonic(opcode_t x) {
return (
#   include "caml/mnem.h"
    "INVALID_BYTECODE" );
}
#endif
#endif


/* The interpreter itself */

value caml_interprete(code_t prog, asize_t prog_size)
{
#ifdef PC_REG
  register code_t pc PC_REG;
  register value * sp SP_REG;
  register value accu ACCU_REG;
#else
  register code_t pc;
  register value * sp;
  register value accu;
#endif
#if defined(THREADED_CODE) && defined(ARCH_SIXTYFOUR) && !defined(ARCH_CODE32)
#ifdef JUMPTBL_BASE_REG
  register char * jumptbl_base JUMPTBL_BASE_REG;
#else
  register char * jumptbl_base;
#endif
#endif
  value env;
  intnat extra_args;
  struct longjmp_buffer * initial_external_raise;
  int initial_sp_offset;
  /* volatile ensures that initial_local_roots and saved_pc
     will keep correct value across longjmp */
  struct caml__roots_block * volatile initial_local_roots;
  volatile code_t saved_pc = NULL;
  struct longjmp_buffer raise_buf;
  int raise_shall_return;
#ifndef THREADED_CODE
  opcode_t curr_instr;
#endif

#ifdef THREADED_CODE
  static void * jumptable[] = {
#    include "caml/jumptbl.h"
  };
#define STOP_TEMPLATE_SIZE 100
  static void * _codetmpl_exit[] = {
#    include "caml/codetmpl_exit.h"
  };

  /* initializes pointers to code templates */
  codetmpl_entry = jumptable;
  codetmpl_exit = _codetmpl_exit;
  check_stacks_entry = &&check_stacks;
  check_stacks_exit = &&InstructEnd(CHECK_SIGNALS);
  process_signal_entry = &&process_signal;
  process_signal_exit = &&InstructEnd(CHECK_SIGNALS);
  perform_return_entry = &&perform_return;
  perform_return_exit = &caml_prepare_bytecode;
  trampoline_internal_entry = &&lbl_trampoline_internal;
  trampoline_internal_exit = &&lbl_end_trampoline_internal;
  POPTRAP_trampoline_entry = &&lbl_POPTRAP_trampoline;
  POPTRAP_trampoline_exit = &&lbl_end_POPTRAP_trampoline;
  RAISE_trampoline_entry = &&lbl_RAISE_trampoline;
  RAISE_trampoline_exit = &&lbl_end_RAISE_trampoline;
  dbg_trampoline_entry = &&lbl_dbg_trampoline;
  dbg_trampoline_exit = &&lbl_end_dbg_trampoline;
#ifdef DUMP_JIT_OPCODES
  echo_entry = &&lbl_echo;
  echo_exit = &&lbl_end_echo;
#endif
#endif

  /* Local pointers to global data, used to force correct addressing in asm */
  void* *_jumptable = jumptable; 
  void* *_tgt_table = tgt_table;
#if defined(THREADED_CODE) && defined(DUMP_JIT_OPCODES)
  code_t _jit_saved_code = jit_saved_code;
  const char *_echo_fmt = "%d %s\n";
#endif
#if defined(CAML_METHOD_CACHE) && defined(CAML_TEST_CACHE)
  const char *_cache_hit_fmt = "cache hit = %d%%\n";
#endif

  /* Pointers to extern data, used to force correct addressing in asm */
  value*                 *_P_caml_young_ptr        = &caml_young_ptr;
  value*                 *_P_caml_young_trigger    = &caml_young_trigger;
  value                  *_P_caml_global_data      = &caml_global_data;
  struct ext_table       *_P_caml_prim_table       = &caml_prim_table;
  value*                 *_P_caml_stack_high       = &caml_stack_high;
  value*                 *_P_caml_stack_threshold  = &caml_stack_threshold;
  value*                 *_P_caml_extern_sp        = &caml_extern_sp;
  value*                 *_P_caml_trapsp           = &caml_trapsp;
  value*                 *_P_caml_trap_barrier     = &caml_trap_barrier;
  volatile int           *_P_caml_something_to_do  = &caml_something_to_do;
  int32_t                *_P_caml_backtrace_active = &caml_backtrace_active;
  struct longjmp_buffer* *_P_caml_external_raise   = &caml_external_raise;
  int                    *_P_caml_callback_depth   = &caml_callback_depth;
  unsigned char*         *_P_caml_saved_code       = &caml_saved_code;
  code_t                 *_P_caml_start_code       = &caml_start_code;
  uintnat                *_P_caml_event_count      = &caml_event_count;
  header_t               (*_P_caml_atom_table)[]   = &caml_atom_table;

  /* Pointers to functions, used to force correct addressing in asm */
#if defined(NATIVE_CODE) && defined(WITH_SPACETIME)
  uintnat (*_F_caml_spacetime_my_profinfo)(void) = caml_spacetime_my_profinfo;
#endif
  void    (*_F_caml_gc_dispatch)(void)           = caml_gc_dispatch;
  value   (*_F_caml_alloc_shr)(mlsize_t, tag_t)  = caml_alloc_shr;
  void    (*_F_caml_initialize)(value*, value)   = caml_initialize;
  void    (*_F_caml_modify)(value*, value)       = caml_modify;
  void    (*_F_caml_debugger)(enum event_kind)   = caml_debugger;
  void    (*_F_caml_stash_backtrace)(value, code_t, value*, int)
                                                 = caml_stash_backtrace;
  void    (*_F_caml_realloc_stack)(asize_t)      = caml_realloc_stack;
  void    (*_F_caml_process_event)(void)         = caml_process_event;
  void    (*_F_caml_raise_zero_divide)(void)     = caml_raise_zero_divide;
#if (defined(THREADED_CODE) && defined(DUMP_JIT_OPCODES)) || (defined(CAML_METHOD_CACHE) && defined(CAML_TEST_CACHE))
  int     (*_F_stderrprintf)(const char*, ...)   = stderrprintf;
#endif
#if defined(THREADED_CODE) && defined(DUMP_JIT_OPCODES)
  char*   (*_F_mnemonic)(opcode_t)               = mnemonic;
#endif

  if (prog == NULL) {           /* Interpreter is initializing */
#ifdef THREADED_CODE
    caml_instr_table = (char **) jumptable;
    caml_instr_base = Jumptbl_base;

    /* calculates the maximum size of the binary code blocks
     * that implement the semantics of the bytecodes, and
     * creates a sufficiently big buffer
     */
    max_template_size = 0;
    for (int i = 0; i < FIRST_UNIMPLEMENTED_OP; ++i) {
      long binary_block_size = codetmpl_exit[i] - codetmpl_entry[i];
      if (binary_block_size > max_template_size) {
        max_template_size = binary_block_size;
      }
    }
    /* TODO add the size of the additional blocks for greater safety */

#endif
    return Val_unit;
  }

#if defined(THREADED_CODE) && defined(ARCH_SIXTYFOUR) && !defined(ARCH_CODE32)
  jumptbl_base = Jumptbl_base;
#endif
  initial_local_roots = caml_local_roots;
  initial_sp_offset = (char *) caml_stack_high - (char *) caml_extern_sp;
  initial_external_raise = caml_external_raise;
  caml_callback_depth++;
  saved_pc = NULL;

  if (sigsetjmp(raise_buf.buf, 0)) {
    caml_local_roots = initial_local_roots;
    sp = caml_extern_sp;
    accu = caml_exn_bucket;
    pc = saved_pc; saved_pc = NULL;
    if (pc != NULL) pc += 2;
        /* +2 adjustement for the sole purpose of backtraces */
    goto raise_exception;
  }
  caml_external_raise = &raise_buf;

  sp = caml_extern_sp;
  pc = prog;
  extra_args = 0;
  env = Atom(0);
  accu = Val_int(0);

#ifdef THREADED_CODE
  /* TODO this is just for testing! Compilation should be triggered externally! */
  int frobaz = 0;
  void compile(void);
  if (frobaz) {
    compile();
    _tgt_table = tgt_table;
  }

  /* if there is a compiled binary, executes it... */
  if (frobaz) {
#if 0
  if (_tgt_table != 0) {
#endif
    JitNext;
  }
  /* ...otherwise goes on */

#ifdef DEBUG
 next_instr:
  if (caml_icount-- == 0) caml_stop_here ();
  Assert(sp >= caml_stack_low);
  Assert(sp <= caml_stack_high);
#endif
  goto *(void *)(jumptbl_base + *pc); /* Jump to the first instruction */
#else
  while(1) {
#ifdef DEBUG
    caml_bcodcount++;
    if (caml_icount-- == 0) caml_stop_here ();
    if (caml_trace_level>1) printf("\n##%ld\n", caml_bcodcount);
    if (caml_trace_level>0) caml_disasm_instr(pc);
    if (caml_trace_level>1) {
      printf("env=");
      caml_trace_value_file(env,prog,prog_size,stdout);
      putchar('\n');
      caml_trace_accu_sp_file(accu,sp,prog,prog_size,stdout);
      fflush(stdout);
    };
    Assert(sp >= caml_stack_low);
    Assert(sp <= caml_stack_high);
#endif
    curr_instr = *pc;

  dispatch_instr:
    switch(curr_instr) {
#endif

/* Unreachable operations used as templates for jit compilation */
    lbl_trampoline_internal:
      JitNext;
    lbl_end_trampoline_internal:

    lbl_POPTRAP_trampoline:
      if (!*_P_caml_something_to_do) {
        JitNext;
      } /* else, fall through */
    lbl_end_POPTRAP_trampoline:

    lbl_RAISE_trampoline:
      if (!raise_shall_return) {
        JitNext;
      } /* else, fall through */
    lbl_end_RAISE_trampoline:

    lbl_dbg_trampoline:
      --pc;
      DebugNext;
    lbl_end_dbg_trampoline:

#if defined(THREADED_CODE) && defined(DUMP_JIT_OPCODES)
    lbl_echo:
      _F_stderrprintf(_echo_fmt, pc - prog, _F_mnemonic(_jit_saved_code[pc - prog]));
    lbl_end_echo:
#endif

/* Basic stack operations */

    Instruct(ACC0):
      ++pc;
      accu = sp[0];
    InstructEnd(ACC0):
      Next;

    Instruct(ACC1):
      ++pc;
      accu = sp[1];
    InstructEnd(ACC1):
      Next;

    Instruct(ACC2):
      ++pc;
      accu = sp[2];
    InstructEnd(ACC2):
      Next;

    Instruct(ACC3):
      ++pc;
      accu = sp[3];
    InstructEnd(ACC3):
      Next;

    Instruct(ACC4):
      ++pc;
      accu = sp[4];
    InstructEnd(ACC4):
      Next;

    Instruct(ACC5):
      ++pc;
      accu = sp[5];
    InstructEnd(ACC5):
      Next;

    Instruct(ACC6):
      ++pc;
      accu = sp[6];
    InstructEnd(ACC6):
      Next;
    Instruct(ACC7):
      ++pc;
      accu = sp[7];
    InstructEnd(ACC7):
      Next;

    Instruct(PUSH): Instruct(PUSHACC0):
      ++pc;
      *--sp = accu;
    InstructEnd(PUSH): InstructEnd(PUSHACC0):
      Next;

    Instruct(PUSHACC1):
      ++pc;
      *--sp = accu; accu = sp[1];
    InstructEnd(PUSHACC1):
      Next;

    Instruct(PUSHACC2):
      ++pc;
      *--sp = accu; accu = sp[2];
    InstructEnd(PUSHACC2):
      Next;

    Instruct(PUSHACC3):
      ++pc;
      *--sp = accu; accu = sp[3];
    InstructEnd(PUSHACC3):
      Next;

    Instruct(PUSHACC4):
      ++pc;
      *--sp = accu; accu = sp[4];
    InstructEnd(PUSHACC4):
      Next;

    Instruct(PUSHACC5):
      ++pc;
      *--sp = accu; accu = sp[5];
    InstructEnd(PUSHACC5):
      Next;

    Instruct(PUSHACC6):
      ++pc;
      *--sp = accu; accu = sp[6];
    InstructEnd(PUSHACC6):
      Next;

    Instruct(PUSHACC7):
      ++pc;
      *--sp = accu; accu = sp[7];
    InstructEnd(PUSHACC7):
      Next;

    Instruct(PUSHACC):
      ++pc;
      *--sp = accu;
      accu = sp[*pc++];
    InstructEnd(PUSHACC):
      Next;

    Instruct(ACC):
      ++pc;
      accu = sp[*pc++];
    InstructEnd(ACC):
      Next;

    Instruct(POP):
      ++pc;
      sp += *pc++;
    InstructEnd(POP):
      Next;

    Instruct(ASSIGN):
      ++pc;
      sp[*pc++] = accu;
      accu = Val_unit;
    InstructEnd(ASSIGN):
      Next;

/* Access in heap-allocated environment */

    Instruct(ENVACC1):
      ++pc;
      accu = Field(env, 1);
    InstructEnd(ENVACC1):
      Next;

    Instruct(ENVACC2):
      ++pc;
      accu = Field(env, 2);
    InstructEnd(ENVACC2):
      Next;

    Instruct(ENVACC3):
      ++pc;
      accu = Field(env, 3);
    InstructEnd(ENVACC3):
      Next;

    Instruct(ENVACC4):
      ++pc;
      accu = Field(env, 4);
    InstructEnd(ENVACC4):
      Next;

    Instruct(PUSHENVACC1):
      ++pc;
      *--sp = accu; accu = Field(env, 1);
    InstructEnd(PUSHENVACC1):
      Next;

    Instruct(PUSHENVACC2):
      ++pc;
      *--sp = accu; accu = Field(env, 2);
    InstructEnd(PUSHENVACC2):
      Next;

    Instruct(PUSHENVACC3):
      ++pc;
      *--sp = accu; accu = Field(env, 3);
    InstructEnd(PUSHENVACC3):
      Next;

    Instruct(PUSHENVACC4):
      ++pc;
      *--sp = accu; accu = Field(env, 4);
    InstructEnd(PUSHENVACC4):
      Next;

    Instruct(PUSHENVACC):
      ++pc;
      *--sp = accu;
      accu = Field(env, *pc++);
    InstructEnd(PUSHENVACC):
      Next;

    Instruct(ENVACC):
      ++pc;
      accu = Field(env, *pc++);
    InstructEnd(ENVACC):
      Next;

/* Function application */

    Instruct(PUSH_RETADDR): {
      ++pc;
      sp -= 3;
      sp[0] = (value) (pc + *pc);
      sp[1] = env;
      sp[2] = Val_long(extra_args);
      pc++;
    InstructEnd(PUSH_RETADDR):
      Next;
    }

    Instruct(APPLY): {
      ++pc;
      extra_args = *pc - 1;
      pc = Code_val(accu);
      env = accu;
    InstructEnd(APPLY):
      goto check_stacks;
    }

    Instruct(APPLY1): {
      ++pc;
      value arg1 = sp[0];
      sp -= 3;
      sp[0] = arg1;
      sp[1] = (value)pc;
      sp[2] = env;
      sp[3] = Val_long(extra_args);
      pc = Code_val(accu);
      env = accu;
      extra_args = 0;
    InstructEnd(APPLY1):
      goto check_stacks;
    }

    Instruct(APPLY2): {
      ++pc;
      value arg1 = sp[0];
      value arg2 = sp[1];
      sp -= 3;
      sp[0] = arg1;
      sp[1] = arg2;
      sp[2] = (value)pc;
      sp[3] = env;
      sp[4] = Val_long(extra_args);
      pc = Code_val(accu);
      env = accu;
      extra_args = 1;
    InstructEnd(APPLY2):
      goto check_stacks;
    }

    Instruct(APPLY3): {
      ++pc;
      value arg1 = sp[0];
      value arg2 = sp[1];
      value arg3 = sp[2];
      sp -= 3;
      sp[0] = arg1;
      sp[1] = arg2;
      sp[2] = arg3;
      sp[3] = (value)pc;
      sp[4] = env;
      sp[5] = Val_long(extra_args);
      pc = Code_val(accu);
      env = accu;
      extra_args = 2;
    InstructEnd(APPLY3):
      goto check_stacks;
    }

    Instruct(APPTERM): {
      ++pc;
      int nargs = *pc++;
      int slotsize = *pc;
      value * newsp;
      int i;
      /* Slide the nargs bottom words of the current frame to the top
         of the frame, and discard the remainder of the frame */
      newsp = sp + slotsize - nargs;
      for (i = nargs - 1; i >= 0; i--) newsp[i] = sp[i];
      sp = newsp;
      pc = Code_val(accu);
      env = accu;
      extra_args += nargs - 1;
    InstructEnd(APPTERM):
      goto check_stacks;
    }

    Instruct(APPTERM1): {
      ++pc;
      value arg1 = sp[0];
      sp = sp + *pc - 1;
      sp[0] = arg1;
      pc = Code_val(accu);
      env = accu;
    InstructEnd(APPTERM1):
      goto check_stacks;
    }

    Instruct(APPTERM2): {
      ++pc;
      value arg1 = sp[0];
      value arg2 = sp[1];
      sp = sp + *pc - 2;
      sp[0] = arg1;
      sp[1] = arg2;
      pc = Code_val(accu);
      env = accu;
      extra_args += 1;
    InstructEnd(APPTERM2):
      goto check_stacks;
    }

    Instruct(APPTERM3): {
      ++pc;
      value arg1 = sp[0];
      value arg2 = sp[1];
      value arg3 = sp[2];
      sp = sp + *pc - 3;
      sp[0] = arg1;
      sp[1] = arg2;
      sp[2] = arg3;
      pc = Code_val(accu);
      env = accu;
      extra_args += 2;
    InstructEnd(APPTERM3):
      goto check_stacks;
    }

    Instruct(RETURN): {
      ++pc;
      sp += *pc++;
      if (extra_args > 0) {
        extra_args--;
        pc = Code_val(accu);
        env = accu;
      } else {
        pc = (code_t)(sp[0]);
        env = sp[1];
        extra_args = Long_val(sp[2]);
        sp += 3;
      }
    InstructEnd(RETURN):
      Next;
    }

    Instruct(RESTART): {
      ++pc;
      int num_args = Wosize_val(env) - 2;
      int i;
      sp -= num_args;
      for (i = 0; i < num_args; i++) sp[i] = Field(env, i + 2);
      env = Field(env, 1);
      extra_args += num_args;
    InstructEnd(RESTART):
      Next;
    }

    Instruct(GRAB): {
      ++pc;
      int required = *pc++;
      if (extra_args >= required) {
        extra_args -= required;
      } else {
        mlsize_t num_args, i;
        num_args = 1 + extra_args; /* arg1 + extra args */
        _F_Alloc_small(accu, num_args + 2, Closure_tag);
        Field(accu, 1) = env;
        for (i = 0; i < num_args; i++) Field(accu, i + 2) = sp[i];
        Code_val(accu) = pc - 3; /* Point to the preceding RESTART instr. */
        sp += num_args;
        pc = (code_t)(sp[0]);
        env = sp[1];
        extra_args = Long_val(sp[2]);
        sp += 3;
      }
    InstructEnd(GRAB):
      Next;
    }

    Instruct(CLOSURE): {
      ++pc;
      int nvars = *pc++;
      int i;
      if (nvars > 0) *--sp = accu;
      if (nvars < Max_young_wosize) {
        /* nvars + 1 <= Max_young_wosize, can allocate in minor heap */
        _F_Alloc_small(accu, 1 + nvars, Closure_tag);
        for (i = 0; i < nvars; i++) Field(accu, i + 1) = sp[i];
      } else {
        /* PR#6385: must allocate in major heap */
        /* caml_alloc_shr and caml_initialize never trigger a GC,
           so no need to Setup_for_gc */
        accu = _F_caml_alloc_shr(1 + nvars, Closure_tag);
        for (i = 0; i < nvars; i++) _F_caml_initialize(&Field(accu, i + 1), sp[i]);
      }
      /* The code pointer is not in the heap, so no need to go through
         caml_initialize. */
      Code_val(accu) = pc + *pc;
      pc++;
      sp += nvars;
    InstructEnd(CLOSURE):
      Next;
    }

    Instruct(CLOSUREREC): {
      ++pc;
      int nfuncs = *pc++;
      int nvars = *pc++;
      mlsize_t blksize = nfuncs * 2 - 1 + nvars;
      int i;
      value * p;
      if (nvars > 0) *--sp = accu;
      if (blksize <= Max_young_wosize) {
        _F_Alloc_small(accu, blksize, Closure_tag);
        p = &Field(accu, nfuncs * 2 - 1);
        for (i = 0; i < nvars; i++, p++) *p = sp[i];
      } else {
        /* PR#6385: must allocate in major heap */
        /* caml_alloc_shr and caml_initialize never trigger a GC,
           so no need to Setup_for_gc */
        accu = _F_caml_alloc_shr(blksize, Closure_tag);
        p = &Field(accu, nfuncs * 2 - 1);
        for (i = 0; i < nvars; i++, p++) _F_caml_initialize(p, sp[i]);
      }
      sp += nvars;
      /* The code pointers and infix headers are not in the heap,
         so no need to go through caml_initialize. */
      p = &Field(accu, 0);
      *p = (value) (pc + pc[0]);
      *--sp = accu;
      p++;
      for (i = 1; i < nfuncs; i++) {
        *p = Make_header(i * 2, Infix_tag, Caml_white);  /* color irrelevant. */
        p++;
        *p = (value) (pc + pc[i]);
        *--sp = (value) p;
        p++;
      }
      pc += nfuncs;
    InstructEnd(CLOSUREREC):
      Next;
    }

    Instruct(PUSHOFFSETCLOSURE):
      ++pc;
      *--sp = accu;
      accu = env + *pc++ * sizeof(value);
    InstructEnd(PUSHOFFSETCLOSURE):
      Next;

    Instruct(OFFSETCLOSURE):
      ++pc;
      accu = env + *pc++ * sizeof(value);
    InstructEnd(OFFSETCLOSURE):
      Next;

    Instruct(PUSHOFFSETCLOSUREM2):
      ++pc;
      *--sp = accu;
      accu = env - 2 * sizeof(value);
    InstructEnd(PUSHOFFSETCLOSUREM2):
      Next;

    Instruct(OFFSETCLOSUREM2):
      ++pc;
      accu = env - 2 * sizeof(value);
    InstructEnd(OFFSETCLOSUREM2):
      Next;

    Instruct(PUSHOFFSETCLOSURE0):
      ++pc;
      *--sp = accu;
      accu = env;
    InstructEnd(PUSHOFFSETCLOSURE0):
      Next;

    Instruct(OFFSETCLOSURE0):
      ++pc;
      accu = env;
    InstructEnd(OFFSETCLOSURE0):
      Next;

    Instruct(PUSHOFFSETCLOSURE2):
      ++pc;
      *--sp = accu;
      accu = env + 2 * sizeof(value);
    InstructEnd(PUSHOFFSETCLOSURE2):
      Next;

    Instruct(OFFSETCLOSURE2):
      ++pc;
      accu = env + 2 * sizeof(value);
    InstructEnd(OFFSETCLOSURE2):
      Next;


/* Access to global variables */

    Instruct(PUSHGETGLOBAL):
      ++pc;
      *--sp = accu;
      accu = Field(*_P_caml_global_data, *pc);
      pc++;
    InstructEnd(PUSHGETGLOBAL):
      Next;

    Instruct(GETGLOBAL):
      ++pc;
      accu = Field(*_P_caml_global_data, *pc);
      pc++;
    InstructEnd(GETGLOBAL):
      Next;

    Instruct(PUSHGETGLOBALFIELD):
      ++pc;
      *--sp = accu;
      accu = Field(*_P_caml_global_data, *pc);
      pc++;
      accu = Field(accu, *pc);
      pc++;
    InstructEnd(PUSHGETGLOBALFIELD):
      Next;

    Instruct(GETGLOBALFIELD): {
      ++pc;
      accu = Field(*_P_caml_global_data, *pc);
      pc++;
      accu = Field(accu, *pc);
      pc++;
    InstructEnd(GETGLOBALFIELD):
      Next;
    }

    Instruct(SETGLOBAL):
      ++pc;
      _F_caml_modify(&Field(*_P_caml_global_data, *pc), accu);
      accu = Val_unit;
      pc++;
    InstructEnd(SETGLOBAL):
      Next;

/* Allocation of blocks */

    Instruct(PUSHATOM0):
      ++pc;
      *--sp = accu;
      accu = _F_Atom(0);
    InstructEnd(PUSHATOM0):
      Next;

    Instruct(ATOM0):
      ++pc;
      accu = _F_Atom(0);
    InstructEnd(ATOM0):
      Next;

    Instruct(PUSHATOM):
      ++pc;
      *--sp = accu;
      accu = _F_Atom(*pc++);
    InstructEnd(PUSHATOM):
      Next;

    Instruct(ATOM):
      ++pc;
      accu = _F_Atom(*pc++);
    InstructEnd(ATOM):
      Next;

    Instruct(MAKEBLOCK): {
      ++pc;
      mlsize_t wosize = *pc++;
      tag_t tag = *pc++;
      mlsize_t i;
      value block;
      if (wosize <= Max_young_wosize) {
        _F_Alloc_small(block, wosize, tag);
        Field(block, 0) = accu;
        for (i = 1; i < wosize; i++) Field(block, i) = *sp++;
      } else {
        block = _F_caml_alloc_shr(wosize, tag);
        _F_caml_initialize(&Field(block, 0), accu);
        for (i = 1; i < wosize; i++) _F_caml_initialize(&Field(block, i), *sp++);
      }
      accu = block;
    InstructEnd(MAKEBLOCK):
      Next;
    }

    Instruct(MAKEBLOCK1): {
      ++pc;
      tag_t tag = *pc++;
      value block;
      _F_Alloc_small(block, 1, tag);
      Field(block, 0) = accu;
      accu = block;
    InstructEnd(MAKEBLOCK1):
      Next;
    }

    Instruct(MAKEBLOCK2): {
      ++pc;
      tag_t tag = *pc++;
      value block;
      _F_Alloc_small(block, 2, tag);
      Field(block, 0) = accu;
      Field(block, 1) = sp[0];
      sp += 1;
      accu = block;
    InstructEnd(MAKEBLOCK2):
      Next;
    }

    Instruct(MAKEBLOCK3): {
      ++pc;
      tag_t tag = *pc++;
      value block;
      _F_Alloc_small(block, 3, tag);
      Field(block, 0) = accu;
      Field(block, 1) = sp[0];
      Field(block, 2) = sp[1];
      sp += 2;
      accu = block;
    InstructEnd(MAKEBLOCK3):
      Next;
    }

    Instruct(MAKEFLOATBLOCK): {
      ++pc;
      mlsize_t size = *pc++;
      mlsize_t i;
      value block;
      if (size <= Max_young_wosize / Double_wosize) {
        _F_Alloc_small(block, size * Double_wosize, Double_array_tag);
      } else {
        block = _F_caml_alloc_shr(size * Double_wosize, Double_array_tag);
      }
      Store_double_field(block, 0, Double_val(accu));
      for (i = 1; i < size; i++){
        Store_double_field(block, i, Double_val(*sp));
        ++ sp;
      }
      accu = block;
    InstructEnd(MAKEFLOATBLOCK):
      Next;
    }

/* Access to components of blocks */

    Instruct(GETFIELD0):
      ++pc;
      accu = Field(accu, 0);
    InstructEnd(GETFIELD0):
      Next;

    Instruct(GETFIELD1):
      ++pc;
      accu = Field(accu, 1);
    InstructEnd(GETFIELD1):
      Next;

    Instruct(GETFIELD2):
      ++pc;
      accu = Field(accu, 2);
    InstructEnd(GETFIELD2):
      Next;

    Instruct(GETFIELD3):
      ++pc;
      accu = Field(accu, 3);
    InstructEnd(GETFIELD3):
      Next;

    Instruct(GETFIELD):
      ++pc;
      accu = Field(accu, *pc); pc++;
    InstructEnd(GETFIELD):
      Next;

    Instruct(GETFLOATFIELD): {
      ++pc;
      double d = Double_field(accu, *pc);
      _F_Alloc_small(accu, Double_wosize, Double_tag);
      Store_double_val(accu, d);
      pc++;
    InstructEnd(GETFLOATFIELD):
      Next;
    }

    Instruct(SETFIELD0):
      ++pc;
      _F_caml_modify(&Field(accu, 0), *sp++);
      accu = Val_unit;
    InstructEnd(SETFIELD0):
      Next;

    Instruct(SETFIELD1):
      ++pc;
      _F_caml_modify(&Field(accu, 1), *sp++);
      accu = Val_unit;
    InstructEnd(SETFIELD1):
      Next;

    Instruct(SETFIELD2):
      ++pc;
      _F_caml_modify(&Field(accu, 2), *sp++);
      accu = Val_unit;
    InstructEnd(SETFIELD2):
      Next;

    Instruct(SETFIELD3):
      ++pc;
      _F_caml_modify(&Field(accu, 3), *sp++);
      accu = Val_unit;
    InstructEnd(SETFIELD3):
      Next;

    Instruct(SETFIELD):
      ++pc;
      _F_caml_modify(&Field(accu, *pc), *sp++);
      accu = Val_unit;
      pc++;
    InstructEnd(SETFIELD):
      Next;

    Instruct(SETFLOATFIELD):
      ++pc;
      Store_double_field(accu, *pc, Double_val(*sp));
      accu = Val_unit;
      sp++;
      pc++;
    InstructEnd(SETFLOATFIELD):
      Next;

/* Array operations */

    Instruct(VECTLENGTH): {
      ++pc;
      mlsize_t size = Wosize_val(accu);
      if (Tag_val(accu) == Double_array_tag) size = size / Double_wosize;
      accu = Val_long(size);
    InstructEnd(VECTLENGTH):
      Next;
    }

    Instruct(GETVECTITEM):
      ++pc;
      accu = Field(accu, Long_val(sp[0]));
      sp += 1;
    InstructEnd(GETVECTITEM):
      Next;

    Instruct(SETVECTITEM):
      ++pc;
      _F_caml_modify(&Field(accu, Long_val(sp[0])), sp[1]);
      accu = Val_unit;
      sp += 2;
    InstructEnd(SETVECTITEM):
      Next;

/* String operations */

    Instruct(GETSTRINGCHAR):
      ++pc;
      accu = Val_int(Byte_u(accu, Long_val(sp[0])));
      sp += 1;
    InstructEnd(GETSTRINGCHAR):
      Next;

    Instruct(SETSTRINGCHAR):
      ++pc;
      Byte_u(accu, Long_val(sp[0])) = Int_val(sp[1]);
      sp += 2;
      accu = Val_unit;
    InstructEnd(SETSTRINGCHAR):
      Next;

/* Branches and conditional branches */

    Instruct(BRANCH):
      ++pc;
      pc += *pc;
    InstructEnd(BRANCH):
      Next;

    Instruct(BRANCHIF):
      ++pc;
      if (accu != Val_false) pc += *pc; else pc++;
    InstructEnd(BRANCHIF):
      Next;

    Instruct(BRANCHIFNOT):
      ++pc;
      if (accu == Val_false) pc += *pc; else pc++;
    InstructEnd(BRANCHIFNOT):
      Next;

    Instruct(SWITCH): {
      ++pc;
      uint32_t sizes = *pc++;
      if (Is_block(accu)) {
        intnat index = Tag_val(accu);
        Assert ((uintnat) index < (sizes >> 16));
        pc += pc[(sizes & 0xFFFF) + index];
      } else {
        intnat index = Long_val(accu);
        Assert ((uintnat) index < (sizes & 0xFFFF)) ;
        pc += pc[index];
      }
    InstructEnd(SWITCH):
      Next;
    }

    Instruct(BOOLNOT):
      ++pc;
      accu = Val_not(accu);
    InstructEnd(BOOLNOT):
      Next;

/* Exceptions */

    Instruct(PUSHTRAP):
      ++pc;
      sp -= 4;
      Trap_pc(sp) = pc + *pc;
      Trap_link(sp) = *_P_caml_trapsp;
      sp[2] = env;
      sp[3] = Val_long(extra_args);
      *_P_caml_trapsp = sp;
      pc++;
    InstructEnd(PUSHTRAP):
      Next;

    Instruct(POPTRAP):
      ++pc;
      if (*_P_caml_something_to_do) {
        /* We must check here so that if a signal is pending and its
           handler triggers an exception, the exception is trapped
           by the current try...with, not the enclosing one. */
        pc--; /* restart the POPTRAP after processing the signal */
      } else {
        *_P_caml_trapsp = Trap_link(sp);
        sp += 4;
      }
    InstructEnd(POPTRAP):
      if (caml_something_to_do) {
        goto process_signal;
      } else {
        Next;
      }

    Instruct(RAISE_NOTRACE):
      ++pc;
      if (*_P_caml_trapsp >= *_P_caml_trap_barrier) _F_caml_debugger(TRAP_BARRIER);
      goto raise_notrace;

    Instruct(RERAISE):
      ++pc;
      if (*_P_caml_trapsp >= *_P_caml_trap_barrier) _F_caml_debugger(TRAP_BARRIER);
      if (*_P_caml_backtrace_active) _F_caml_stash_backtrace(accu, pc, sp, 1);
      goto raise_notrace;

    Instruct(RAISE):
      ++pc;
    raise_exception:
      if (*_P_caml_trapsp >= *_P_caml_trap_barrier) _F_caml_debugger(TRAP_BARRIER);
      if (*_P_caml_backtrace_active) _F_caml_stash_backtrace(accu, pc, sp, 0);
    raise_notrace:
      raise_shall_return = ((char *) *_P_caml_trapsp
          >= (char *) *_P_caml_stack_high - initial_sp_offset);
      if (raise_shall_return) {
        *_P_caml_external_raise = initial_external_raise;
        *_P_caml_extern_sp = (value *) ((char *) *_P_caml_stack_high
                                    - initial_sp_offset);
        (*_P_caml_callback_depth)--;
        accu = Make_exception_result(accu);
      } else {
        sp = *_P_caml_trapsp;
        pc = Trap_pc(sp);
        *_P_caml_trapsp = Trap_link(sp);
        env = sp[2];
        extra_args = Long_val(sp[3]);
        sp += 4;
      }
    InstructEnd(RAISE_NOTRACE):
    InstructEnd(RERAISE):
    InstructEnd(RAISE):
      if (raise_shall_return) {
        goto perform_return;
      } else {
        Next;
      }

/* Stack checks */

    check_stacks:
      if (sp < *_P_caml_stack_threshold) {
        *_P_caml_extern_sp = sp;
        _F_caml_realloc_stack(Stack_threshold / sizeof(value));
        sp = *_P_caml_extern_sp;
      }
      goto perform_check_signal;

/* Signal handling */

    Instruct(CHECK_SIGNALS):    /* accu not preserved */
      ++pc;
    perform_check_signal:
      if (*_P_caml_something_to_do) {
    process_signal:
          *_P_caml_something_to_do = 0;
          Setup_for_event;
          _F_caml_process_event();
          Restore_after_event;
      }
    InstructEnd(CHECK_SIGNALS):
      Next;

/* Calling C functions */

    Instruct(C_CALL1):
      ++pc;
      Setup_for_c_call;
      accu = _F_Primitive(*pc)(accu);
      Restore_after_c_call;
      pc++;
    InstructEnd(C_CALL1):
      Next;

    Instruct(C_CALL2):
      ++pc;
      Setup_for_c_call;
      accu = _F_Primitive(*pc)(accu, sp[1]);
      Restore_after_c_call;
      sp += 1;
      pc++;
    InstructEnd(C_CALL2):
      Next;

    Instruct(C_CALL3):
      ++pc;
      Setup_for_c_call;
      accu = _F_Primitive(*pc)(accu, sp[1], sp[2]);
      Restore_after_c_call;
      sp += 2;
      pc++;
    InstructEnd(C_CALL3):
      Next;

    Instruct(C_CALL4):
      ++pc;
      Setup_for_c_call;
      accu = _F_Primitive(*pc)(accu, sp[1], sp[2], sp[3]);
      Restore_after_c_call;
      sp += 3;
      pc++;
    InstructEnd(C_CALL4):
      Next;

    Instruct(C_CALL5):
      ++pc;
      Setup_for_c_call;
      accu = _F_Primitive(*pc)(accu, sp[1], sp[2], sp[3], sp[4]);
      Restore_after_c_call;
      sp += 4;
      pc++;
    InstructEnd(C_CALL5):
      Next;

    Instruct(C_CALLN): {
      ++pc;
      int nargs = *pc++;
      *--sp = accu;
      Setup_for_c_call;
      accu = _F_Primitive(*pc)(sp + 1, nargs);
      Restore_after_c_call;
      sp += nargs;
      pc++;
    InstructEnd(C_CALLN):
      Next;
    }

/* Integer constants */

    Instruct(CONST0):
      ++pc;
      accu = Val_int(0);
    InstructEnd(CONST0):
      Next;

    Instruct(CONST1):
      ++pc;
      accu = Val_int(1);
    InstructEnd(CONST1):
      Next;

    Instruct(CONST2):
      ++pc;
      accu = Val_int(2);
    InstructEnd(CONST2):
      Next;

    Instruct(CONST3):
      ++pc;
      accu = Val_int(3);
    InstructEnd(CONST3):
      Next;

    Instruct(PUSHCONST0):
      ++pc;
      *--sp = accu; accu = Val_int(0);
    InstructEnd(PUSHCONST0):
      Next;

    Instruct(PUSHCONST1):
      ++pc;
      *--sp = accu; accu = Val_int(1);
    InstructEnd(PUSHCONST1):
      Next;

    Instruct(PUSHCONST2):
      ++pc;
      *--sp = accu; accu = Val_int(2);
    InstructEnd(PUSHCONST2):
      Next;

    Instruct(PUSHCONST3):
      ++pc;
      *--sp = accu; accu = Val_int(3);
    InstructEnd(PUSHCONST3):
      Next;

    Instruct(PUSHCONSTINT):
      ++pc;
      *--sp = accu;
      accu = Val_int(*pc);
      pc++;
    InstructEnd(PUSHCONSTINT):
      Next;

    Instruct(CONSTINT):
      ++pc;
      accu = Val_int(*pc);
      pc++;
    InstructEnd(CONSTINT):
      Next;

/* Integer arithmetic */

    Instruct(NEGINT):
      ++pc;
      accu = (value)(2 - (intnat)accu);
    InstructEnd(NEGINT):
      Next;

    Instruct(ADDINT):
      ++pc;
      accu = (value)((intnat) accu + (intnat) *sp++ - 1);
    InstructEnd(ADDINT):
      Next;

    Instruct(SUBINT):
      ++pc;
      accu = (value)((intnat) accu - (intnat) *sp++ + 1);
    InstructEnd(SUBINT):
      Next;

    Instruct(MULINT):
      ++pc;
      accu = Val_long(Long_val(accu) * Long_val(*sp++));
    InstructEnd(MULINT):
      Next;

    Instruct(DIVINT): {
      ++pc;
      intnat divisor = Long_val(*sp++);
      if (divisor == 0) { Setup_for_c_call; _F_caml_raise_zero_divide(); }
      accu = Val_long(Long_val(accu) / divisor);
    InstructEnd(DIVINT):
      Next;
    }

    Instruct(MODINT): {
      ++pc;
      intnat divisor = Long_val(*sp++);
      if (divisor == 0) { Setup_for_c_call; _F_caml_raise_zero_divide(); }
      accu = Val_long(Long_val(accu) % divisor);
    InstructEnd(MODINT):
      Next;
    }

    Instruct(ANDINT):
      ++pc;
      accu = (value)((intnat) accu & (intnat) *sp++);
    InstructEnd(ANDINT):
      Next;

    Instruct(ORINT):
      ++pc;
      accu = (value)((intnat) accu | (intnat) *sp++);
    InstructEnd(ORINT):
      Next;

    Instruct(XORINT):
      ++pc;
      accu = (value)(((intnat) accu ^ (intnat) *sp++) | 1);
    InstructEnd(XORINT):
      Next;

    Instruct(LSLINT):
      ++pc;
      accu = (value)((((intnat) accu - 1) << Long_val(*sp++)) + 1);
    InstructEnd(LSLINT):
      Next;

    Instruct(LSRINT):
      ++pc;
      accu = (value)((((uintnat) accu - 1) >> Long_val(*sp++)) | 1);
    InstructEnd(LSRINT):
      Next;

    Instruct(ASRINT):
      ++pc;
      accu = (value)((((intnat) accu - 1) >> Long_val(*sp++)) | 1);
    InstructEnd(ASRINT):
      Next;

#define Integer_comparison(typ,opname,tst) \
    Instruct(opname): \
      ++pc; \
      accu = Val_int((typ) accu tst (typ) *sp++); \
    InstructEnd(opname): \
      Next;

    Integer_comparison(intnat,EQ, ==)
    Integer_comparison(intnat,NEQ, !=)
    Integer_comparison(intnat,LTINT, <)
    Integer_comparison(intnat,LEINT, <=)
    Integer_comparison(intnat,GTINT, >)
    Integer_comparison(intnat,GEINT, >=)
    Integer_comparison(uintnat,ULTINT, <)
    Integer_comparison(uintnat,UGEINT, >=)

#define Integer_branch_comparison(typ,opname,tst,debug) \
    Instruct(opname): \
      ++pc; \
      if ( *pc++ tst (typ) Long_val(accu)) { \
        pc += *pc ; \
      } else { \
        pc++ ; \
      } ; \
    InstructEnd(opname): \
      Next;

    Integer_branch_comparison(intnat,BEQ, ==, "==")
    Integer_branch_comparison(intnat,BNEQ, !=, "!=")
    Integer_branch_comparison(intnat,BLTINT, <, "<")
    Integer_branch_comparison(intnat,BLEINT, <=, "<=")
    Integer_branch_comparison(intnat,BGTINT, >, ">")
    Integer_branch_comparison(intnat,BGEINT, >=, ">=")
    Integer_branch_comparison(uintnat,BULTINT, <, "<")
    Integer_branch_comparison(uintnat,BUGEINT, >=, ">=")

    Instruct(OFFSETINT):
      ++pc;
      accu += *pc << 1;
      pc++;
    InstructEnd(OFFSETINT):
      Next;

    Instruct(OFFSETREF):
      ++pc;
      Field(accu, 0) += *pc << 1;
      accu = Val_unit;
      pc++;
    InstructEnd(OFFSETREF):
      Next;

    Instruct(ISINT):
      ++pc;
      accu = Val_long(accu & 1);
    InstructEnd(ISINT):
      Next;

/* Object-oriented operations */

#define Lookup(obj, lab) Field (Field (obj, 0), Int_val(lab))

      /* please don't forget to keep below code in sync with the
         functions caml_cache_public_method and
         caml_cache_public_method2 in obj.c */

    Instruct(GETMETHOD):
      ++pc;
      accu = Lookup(sp[0], accu);
    InstructEnd(GETMETHOD):
      Next;

#define CAML_METHOD_CACHE
#ifdef CAML_METHOD_CACHE
    Instruct(GETPUBMET): {
      ++pc;
      /* accu == object, pc[0] == tag, pc[1] == cache */
      value meths = Field (accu, 0);
      value ofs;
#ifdef CAML_TEST_CACHE
      static int calls = 0, hits = 0;
      if (calls >= 10000000) {
        _F_stderrprintf(_cache_hit_fmt, hits / 100000);
        calls = 0; hits = 0;
      }
      calls++;
#endif
      *--sp = accu;
      accu = Val_int(*pc++);
      ofs = *pc & Field(meths,1);
      if (*(value*)(((char*)&Field(meths,3)) + ofs) == accu) {
#ifdef CAML_TEST_CACHE
        hits++;
#endif
        accu = *(value*)(((char*)&Field(meths,2)) + ofs);
      }
      else
      {
        int li = 3, hi = Field(meths,0), mi;
        while (li < hi) {
          mi = ((li+hi) >> 1) | 1;
          if (accu < Field(meths,mi)) hi = mi-2;
          else li = mi;
        }
        *pc = (li-3)*sizeof(value); /* TODO trigger jit recompilation */
        accu = Field (meths, li-1);
      }
      pc++;
    InstructEnd(GETPUBMET):
      Next;
    }
#else
    Instruct(GETPUBMET):
      ++pc;
      *--sp = accu;
      accu = Val_int(*pc);
      pc += 2;
      goto perform_getdynmet;
#endif
    Instruct(GETDYNMET):
      ++pc;
#ifndef CAML_METHOD_CACHE
    perform_getdynmet: {
#else
    {
#endif
      /* accu == tag, sp[0] == object, *pc == cache */
      value meths = Field (sp[0], 0);
      int li = 3, hi = Field(meths,0), mi;
      while (li < hi) {
        mi = ((li+hi) >> 1) | 1;
        if (accu < Field(meths,mi)) hi = mi-2;
        else li = mi;
      }
      accu = Field (meths, li-1);
    InstructEnd(GETDYNMET):
#ifndef CAML_METHOD_CACHE
    InstructEnd(GETPUBMET):
#endif
      Next;
    }

/* Debugging and machine control */

    Instruct(EVENT):
      ++pc;
      if (--(*_P_caml_event_count) == 0) {
        Setup_for_debugger;
        _F_caml_debugger(EVENT_COUNT);
        Restore_after_debugger;
      }
    InstructEnd(EVENT):
      Restart_curr_instr;

    Instruct(BREAK):
      ++pc;
      Setup_for_debugger;
      _F_caml_debugger(BREAKPOINT);
      Restore_after_debugger;
    InstructEnd(BREAK):
      Restart_curr_instr;

    Instruct(STOP):
      ++pc;
      *_P_caml_external_raise = initial_external_raise;
      *_P_caml_extern_sp = sp;
      (*_P_caml_callback_depth)--;
    perform_return:
      return accu;

#ifndef THREADED_CODE
    default:
#if _MSC_VER >= 1200
      __assume(0);
#else
      caml_fatal_error_arg("Fatal error: bad opcode (%"
                           ARCH_INTNAT_PRINTF_FORMAT "x)\n",
                           (char *) (intnat) *(pc-1));
#endif
    }
  }
#endif
}

void caml_prepare_bytecode(code_t prog, asize_t prog_size) {
  /* other implementations of the interpreter (such as an hypothetical
     JIT translator) might want to do something with a bytecode before
     running it */
  Assert(prog);
  Assert(prog_size>0);
  /* actually, the threading of the bytecode might be done here */
}

void caml_release_bytecode(code_t prog, asize_t prog_size) {
  /* other implementations of the interpreter (such as an hypothetical
     JIT translator) might want to know when a bytecode is removed */
  /* check that we have a program */
  Assert(prog);
  Assert(prog_size>0);
}

#ifdef THREADED_CODE

#define MayJump(opcode) \
  (((opcode) == APPLY)       || ((opcode) == APPLY1)   || ((opcode) == APPLY2)        || \
	 ((opcode) == APPLY3)      || ((opcode) == APPTERM)  || ((opcode) == APPTERM1)      || \
	 ((opcode) == APPTERM2)    || ((opcode) == APPTERM3) || ((opcode) == RETURN)        || \
	 ((opcode) == GRAB)        || ((opcode) == BRANCH)   || ((opcode) == BRANCHIF)      || \
	 ((opcode) == BRANCHIFNOT) || ((opcode) == SWITCH)   || ((opcode) == BEQ)           || \
	 ((opcode) == BNEQ)        || ((opcode) == BLTINT)   || ((opcode) == BLEINT)        || \
	 ((opcode) == BGTINT)      || ((opcode) == BGEINT)   || ((opcode) == BULTINT)       || \
	 ((opcode) == BUGEINT))

#define MustCheckStack(opcode) \
  (((opcode) == APPLY)       || ((opcode) == APPLY1)   || ((opcode) == APPLY2)        || \
   ((opcode) == APPLY3)      || ((opcode) == APPTERM)  || ((opcode) == APPTERM1)      || \
   ((opcode) == APPTERM2)    || ((opcode) == APPTERM3))

#define CopyCode(entry, exit) \
    { \
      unsigned char *from; \
      for (from = (unsigned char *) (entry); \
           from != (unsigned char *) (exit); ++from, ++to) { \
        *to = *from; \
        ++compiled_code_size; \
      } \
    }

int bytecode_size(int ofst) {
  /* shamelessly stolen from caml_thread_code */
  opcode_t instr = jit_saved_code[ofst];
  if (instr == SWITCH) {
    uint32_t sizes = jit_saved_code[ofst + 1];
    uint32_t const_size = sizes & 0xFFFF;
    uint32_t block_size = sizes >> 16;
    return const_size + block_size + 2;
  } else if (instr == CLOSUREREC) {
    uint32_t nfuncs = jit_saved_code[ofst + 1];
    return nfuncs + 3;
  } else {
    int* l = caml_init_opcode_nargs();
    return l[instr] + 1;
  }
}

void compile() {
  int compiled_code_size;

  unsigned char *code_buffer =
    (unsigned char *) mmap(0, jit_saved_code_len * sizeof(unsigned char) * max_template_size,
         PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

  /* allocates the tgt_table */
  tgt_table = caml_stat_alloc(jit_saved_code_len * sizeof(void *)); /* TODO is it ok, or should we use malloc? */

  /* dispatches on source code and copies the
   * corresponding blocks in a buffer; at the
   * same times builds the target table
   */
  compiled_code_size = 0;
  unsigned char *to = code_buffer;
  unsigned long long ofst;
  for (ofst = 0; ofst < jit_saved_code_len; ) {
    /* updates tgt_table */
    tgt_table[ofst] = to;

    /* appends in code_buffer the translation of the bytecode */
    opcode_t cur_bytecode = jit_saved_code[ofst];
#ifdef DUMP_JIT_OPCODES
    CopyCode(echo_entry, echo_exit);
#endif
    CopyCode(codetmpl_entry[cur_bytecode], codetmpl_exit[cur_bytecode]);

    /* possibly appends the check stacks code */
    if (MustCheckStack(cur_bytecode)) {
      CopyCode(check_stacks_entry, check_stacks_exit);
    }

    /* handles POPTRAP */
    if (cur_bytecode == POPTRAP) {
      CopyCode(POPTRAP_trampoline_entry, POPTRAP_trampoline_exit);
      CopyCode(process_signal_entry, process_signal_exit);
    }

    /* handles RAISE_NOTRACE, RERAISE, RAISE */
    if (cur_bytecode == RAISE_NOTRACE || cur_bytecode == RERAISE || cur_bytecode == RAISE) {
      CopyCode(RAISE_trampoline_entry, RAISE_trampoline_exit);
      CopyCode(perform_return_entry, perform_return_exit);
    }

    /* handles EVENT and BREAK */
    if (cur_bytecode == EVENT || cur_bytecode == BREAK) {
      CopyCode(dbg_trampoline_entry, dbg_trampoline_exit);
    }

    /* if the bytecode may jump appends the trampoline (except for raise bytecodes
     * that have their own)
     */
    if (MayJump(cur_bytecode)) {
      CopyCode(trampoline_internal_entry, trampoline_internal_exit);
    }

    ofst += bytecode_size(ofst);
  }

  /* makes the buffer executable */
  mprotect(code_buffer, compiled_code_size, PROT_READ | PROT_EXEC);

  /* stores the compiled code */
  binary = code_buffer;
}

#endif
