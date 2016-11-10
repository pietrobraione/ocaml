/*
 * jit.c
 *
 *  Created on: 25 ott 2016
 *      Author: pietro
 */

#define CAML_INTERNALS

#define _DEFAULT_SOURCE

#include <string.h>
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
void *trampoline_breakout_entry = 0;
void *trampoline_breakout_exit = 0;
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
           from != (unsigned char *) (exit); \
	   ++from, ++to, ++compiled_code_size) { \
        *to = *from; \
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

struct jit_fragment *jit_fragment_add(struct jit_context *ctx, code_t code_start, code_t code_end) {
  struct jit_fragment *fgm = caml_stat_alloc(sizeof(struct jit_fragment));
  if (ctx->first == 0) {
    ctx->first = ctx->last = fgm;
  } else {
    ctx->last->next = fgm;
    ctx->last = fgm;
  }

  asize_t code_len = code_end - code_start;
#ifdef DUMP_JIT_OPCODES
  /* stores a copy of the code */
  fgm->code_copy = caml_stat_alloc(code_len * sizeof(opcode_t));
  memcpy(fgm->code, code_start, code_len);
#endif
  fgm->code_start = code_start;
  fgm->code_end = code_end;
  fgm->tgt_table = caml_stat_alloc(code_len * sizeof(void *));
  int i;
  for (i = 0; i < code_len; ++i) fgm->tgt_table[i] = 0;
  caml_ext_table_init(&(fgm->binary_roots), 10);
  fgm->next = 0;

  return fgm;
}

void jit_fragment_remove(struct jit_context *ctx, code_t code_start, code_t code_end) {
  struct jit_fragment *prev, *cur;
  for (prev = 0, cur = ctx->first; cur != 0; prev = cur, cur = cur->next) {
    if (cur->code_start == code_start && cur->code_end == code_end) {
      caml_stat_free(cur->tgt_table);
      int i;
      for (i = 0; i < cur->binary_roots.size; ++i) {
        struct binary_root *r = (struct binary_root *) cur->binary_roots.contents[i];

        munmap(r->root, r->size);
        caml_stat_free(r);
      }
      if (prev == 0) {
        /* it is the root */
        ctx->first = ctx->first->next;
      } else {
        prev->next = cur->next;
      }
      if (ctx->last == cur) {
        ctx->last = prev;
      }
      return;
    }
  }
}

struct jit_fragment *jit_fragment_find(struct jit_context *ctx, code_t pc) {
  struct jit_fragment *cur;
  for (cur = ctx->first; cur != 0; cur = cur->next) {
    if (cur->code_start <= pc && pc < cur->code_end) {
      return cur;
    }
  }
  return 0;
}
#define BinaryCodeBufferSize (code_len * sizeof(unsigned char) * max_template_size)

void jit_compile(struct jit_fragment *fgm, asize_t code_region_start, asize_t code_region_end) {
  asize_t code_len = code_region_end - code_region_start + 1;

  /* allocates memory for the compiled code */
  unsigned char *code_buffer =
    (unsigned char *) mmap(0, BinaryCodeBufferSize,
         PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

  /*
  if (code_buffer == MAP_FAILED) {
    return;
  }
  */

  /* dispatches on source code and copies the
   * corresponding blocks in a buffer; at the
   * same times fills the target table
   */
  int compiled_code_size = 0;
  code_t code = fgm->code_start;
  unsigned char *to = code_buffer;
  unsigned long long ofst;
  for (ofst = code_region_start; ofst < code_region_end; ofst += bytecode_size(code, ofst)) {
    opcode_t cur_bytecode = code[ofst];

    /* updates the target table */
    fgm->tgt_table[ofst] = to;

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
    /* (note that right now jit is inactive during debugging,
     * thus this case is unused)
     */
    if (cur_bytecode == EVENT || cur_bytecode == BREAK) {
      CopyCode(dbg_trampoline_entry, dbg_trampoline_exit);
    }

    /* if the bytecode may jump appends the internal trampoline 
     * (except for raise bytecodes that have their own)
     */
    if (MayJump(cur_bytecode)) {
      CopyCode(trampoline_internal_entry, trampoline_internal_exit);
    }
  }

  /* appends the breakout trampoline */
  CopyCode(trampoline_breakout_entry, trampoline_breakout_exit);


  /* makes the buffer executable */
  mprotect(code_buffer, compiled_code_size, PROT_READ | PROT_EXEC);

  /* stores the root of the compiled code buffer */
  struct binary_root *r = caml_stat_alloc(sizeof (struct binary_root));
  r->root = code_buffer;
  r->size = BinaryCodeBufferSize;
  caml_ext_table_add(&(fgm->binary_roots), r);
}

#endif /* THREADED_CODE */
