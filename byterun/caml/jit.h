/*
 * jit.h
 *
 *  Created on: 25 ott 2016
 *      Author: pietro
 */

#ifndef CAML_JIT_H
#define CAML_JIT_H

#include "misc.h"
#include "mlvalues.h"

#ifdef THREADED_CODE

/* Pointers to code templates; these variables are
 * immutable after initialization and independent on the
 * call context of caml_interprete, that initializes them
 */
CAMLextern void * *codetmpl_entry;
CAMLextern void * *codetmpl_exit;
CAMLextern void *check_stacks_entry;
CAMLextern void *check_stacks_exit;
CAMLextern void *process_signal_entry;
CAMLextern void *process_signal_exit;
CAMLextern void *perform_return_entry;
CAMLextern void *perform_return_exit;
CAMLextern void *trampoline_internal_entry;
CAMLextern void *trampoline_internal_exit;
CAMLextern void *POPTRAP_trampoline_entry;
CAMLextern void *POPTRAP_trampoline_exit;
CAMLextern void *RAISE_trampoline_entry;
CAMLextern void *RAISE_trampoline_exit;
CAMLextern void *dbg_trampoline_entry;
CAMLextern void *dbg_trampoline_exit;
CAMLextern void *echo_entry;
CAMLextern void *echo_exit;

/* The maximum size of a code template; also initialized
 * by caml_interprete
 */
CAMLextern long max_template_size;

/* The result of the compilation produced by the jit */
struct jit_context {
#ifdef DUMP_JIT_OPCODES
  code_t code;
#endif
  void* *tgt_table;
  void *binary;
};

CAMLextern void jit_compile (code_t code, asize_t code_len, struct jit_context *result);

#endif /* THREADED_CODE */
#endif /* CAML_JIT_H */
