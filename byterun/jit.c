/*
 * jit.c
 *
 *  Created on: 25 ott 2016
 *      Author: pietro
 */

#define CAML_INTERNALS

#define _DEFAULT_SOURCE

#include <sys/mman.h>
#include "caml/fix_code.h"
#include "caml/instruct.h"
#include "caml/jit.h"
#include "caml/memory.h"

#ifdef THREADED_CODE

/* Pointers to code templates */
void * *codetmpl_entry = 0;
void * *codetmpl_exit = 0;
void *check_stacks_entry = 0;
void *check_stacks_exit = 0;
void *process_signal_entry = 0;
void *process_signal_exit = 0;
void *perform_return_entry = 0;
void *perform_return_exit = 0;
void *trampoline_internal_entry = 0;
void *trampoline_internal_exit = 0;
void *POPTRAP_trampoline_entry = 0;
void *POPTRAP_trampoline_exit = 0;
void *RAISE_trampoline_entry = 0;
void *RAISE_trampoline_exit = 0;
void *dbg_trampoline_entry = 0;
void *dbg_trampoline_exit = 0;
#ifdef DUMP_JIT_OPCODES
void *echo_entry = 0;
void *echo_exit = 0;
#endif

/* The maximum size of a code template */
long max_template_size;

#define MayJump(opcode) \
  (((opcode) == APPLY)       || ((opcode) == APPLY1)   || ((opcode) == APPLY2)   || \
   ((opcode) == APPLY3)      || ((opcode) == APPTERM)  || ((opcode) == APPTERM1) || \
   ((opcode) == APPTERM2)    || ((opcode) == APPTERM3) || ((opcode) == RETURN)   || \
   ((opcode) == GRAB)        || ((opcode) == BRANCH)   || ((opcode) == BRANCHIF) || \
   ((opcode) == BRANCHIFNOT) || ((opcode) == SWITCH)   || ((opcode) == POPTRAP)  || \
   ((opcode) == BEQ)         || ((opcode) == BNEQ)     || ((opcode) == BLTINT)   || \
   ((opcode) == BLEINT)      || ((opcode) == BGTINT)   || ((opcode) == BGEINT)   || \
   ((opcode) == BULTINT)     || ((opcode) == BUGEINT))

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

/* shamelessly stolen from caml_thread_code */
int bytecode_size(code_t code, int ofst) {
  opcode_t instr = code[ofst];
  if (instr == SWITCH) {
    uint32_t sizes = code[ofst + 1];
    uint32_t const_size = sizes & 0xFFFF;
    uint32_t block_size = sizes >> 16;
    return const_size + block_size + 2;
  } else if (instr == CLOSUREREC) {
    uint32_t nfuncs = code[ofst + 1];
    return nfuncs + 3;
  } else {
    int* l = caml_init_opcode_nargs();
    return l[instr] + 1;
  }
}

void jit_compile(code_t code, asize_t code_len, struct jit_context *result) {
  int compiled_code_size;

  unsigned char *code_buffer =
    (unsigned char *) mmap(0, code_len * sizeof(unsigned char) * max_template_size,
         PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

#ifdef DUMP_JIT_OPCODES
  /* allocates space for a copy of the code */
  result->code = caml_stat_alloc(code_len * sizeof(opcode_t));
#endif

  /* allocates the tgt_table */
  result->tgt_table = caml_stat_alloc(code_len * sizeof(void *));

  /* dispatches on source code and copies the
   * corresponding blocks in a buffer; at the
   * same times builds the target table
   */
  compiled_code_size = 0;
  unsigned char *to = code_buffer;
  unsigned long long ofst;
  for (ofst = 0; ofst < code_len; ) {
    opcode_t cur_bytecode = code[ofst];

#ifdef DUMP_JIT_OPCODES
    /* updates code */
    result->code[ofst] = cur_bytecode;
#endif

    /* updates tgt_table */
    result->tgt_table[ofst] = to;

    /* appends in code_buffer the translation of the bytecode */
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

    ofst += bytecode_size(code, ofst);
  }

  /* makes the buffer executable */
  mprotect(code_buffer, compiled_code_size, PROT_READ | PROT_EXEC);

  /* stores the compiled code */
  result->binary = code_buffer;
}

#endif /* THREADED_CODE */
