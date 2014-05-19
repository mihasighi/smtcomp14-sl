/**************************************************************************/
/*                                                                        */
/*  Compiler for SMTLIB2 frmat for Separation Logic                       */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 3.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 3.                  */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

/** Additional definitions needed to parse SL files
 */

#ifndef _SL_H_
#define _SL_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
#include "sl_type.h"
#include "sl_var.h"
#include "sl_pred.h"
#include "sl_form.h"
#include "sl_prob.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** AST built from the SMTLIB format.
 *  It is defined only for terms and formulas.
 */

/* Valid term builder in SL */
  typedef enum
  {
    SL_F_FALSE = 0,		/* boolean operators */
    SL_F_TRUE,
    SL_F_NOT,
    SL_F_AND,
    SL_F_OR,
    SL_F_IMPLIES,
    SL_F_EXISTS,
    SL_F_FORALL,
    SL_F_LVAR,			/* variable, field, or predicate */
    SL_F_SVAR,
    SL_F_FIELD,
    SL_F_PRED,
    SL_F_EQ,			/* pure operators */
    SL_F_DISTINCT,
    SL_F_EMP,			/* space operators */
    SL_F_JUNK,
    SL_F_SSEP,
    SL_F_PTO,
    SL_F_REF,
    SL_F_SREF,
    SL_F_TOBOOL,
    SL_F_TOSPACE,
    SL_F_LOOP,			/* loop of length at least one */
    SL_F_OTHER
/* NOT TO BE USED */
  } sl_expkind_t;

  typedef struct sl_exp_t
  {
    sl_expkind_t discr;

    union
    {
      /* user-defined function or symbol name */
      uint_t sid;

      /* quantifiers */
      struct
      {
	/* reference to the array containing the variables quantified
	 * in a continuous region from [start to end) */
	sl_var_array *lvars;	/* location vars */
	uint_t lstart;		/* index starting the location quantified variables */
	uint_t lend;		/* index ending the location quantified variables */
      } quant;
    } p;

    struct sl_exp_t **args;	/* array of expression args or NULL */
    uint_t size;		/* size of the array above */

  } sl_exp_t;

/* Context used to parse smtlib2 formulas */
  typedef struct sl_context_t
  {
    /* array storing the size of the frame of the stack
     * for location variables at each
     * quantifier level (only 3 levels are possible):
     * 0 -- size of globals,
     * 1 -- size of define-fun or exists in assert,
     * 2 -- exists in define-fun */
    sl_uint_array *lvar_stack;
    /* location variables environment */
    sl_var_array *lvar_env;

    /* predicate in definition */
    char *pname;
  } sl_context_t;

/**
 * Constants used for variables & parameters identifiers
 */
#define VID_NIL 0
#define VID_FST_PARAM 1
#define VID_SND_PARAM 2

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

  extern int sl_error_parsing;

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialize global variables */
  void sl_init (void);

/* Parsing context */
  sl_context_t *sl_mk_context (void);
  void sl_del_context (sl_context_t * ctx);
/* Allocator/deallocator. */
  void sl_pop_context (sl_context_t * ctx);
/* Pop the local variables. */

/* Parsing logic */
  int sl_set_logic (sl_context_t * ctx, const char *logic);

/* Functions */
  sl_type_t *sl_mk_fun_decl (sl_context_t * ctx, const char *name,
			     sl_type_t * ty);
/* Register a field or a variable. */
  uint_t sl_mk_fun_def (sl_context_t * ctx, const char *name, uint_t npar,
			sl_type_t * rety, sl_exp_t * def);
/* Register a predicate definition. */

/* Commands */
  int sl_assert (sl_context_t * ctx, sl_exp_t * term);
  int sl_check (sl_context_t * ctx);

/* Terms */
  void sl_push_var (sl_context_t * ctx, const char *name, sl_type_t * vty);
/* Declare a local variable in the context. */
  int sl_push_quant (sl_context_t * ctx);
  int sl_pop_quant (sl_context_t * ctx);
/* Increments/decrements the nesting of quantifiers. */

  sl_exp_t *sl_mk_exists (sl_context_t * ctx, sl_exp_t * term);
  sl_exp_t *sl_mk_app (sl_context_t * ctx, const char *name,
		       sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_symbol (sl_context_t * ctx, const char *name);
  sl_exp_t *sl_mk_pred (sl_context_t * ctx, const char *name,
			sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_true (sl_context_t * ctx);
  sl_exp_t *sl_mk_false (sl_context_t * ctx);
  sl_exp_t *sl_mk_and (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_or (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_not (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_eq (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_distinct (sl_context_t * ctx, sl_exp_t ** args,
			    uint_t size);
  sl_exp_t *sl_mk_emp (sl_context_t * ctx);
  sl_exp_t *sl_mk_junk (sl_context_t * ctx);
  sl_exp_t *sl_mk_ssep (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_pto (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_ref (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_sref (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_tobool (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_tospace (sl_context_t * ctx, sl_exp_t ** args, uint_t size);
  sl_exp_t *sl_mk_loop (sl_context_t * ctx, sl_exp_t ** args, uint_t size);

/* ====================================================================== */
/* Typechecking */
/* ====================================================================== */

  sl_exp_t *sl_exp_typecheck (sl_context_t * ctx, sl_exp_t * f);
/* Typecheck a formula and do some simplifications if needed. */

/* ====================================================================== */
/* Translation */
/* ====================================================================== */
/* Build a space formula from AST in args */
  void sl_exp_push_pure (sl_context_t * ctx, sl_exp_t * e, sl_pure_array * f);
  sl_space_t *sl_mk_form_junk (sl_exp_t * e);
  sl_space_t *sl_mk_form_pto (sl_context_t * ctx, sl_exp_t * e);
  sl_space_t *sl_mk_form_loop (sl_context_t * ctx, sl_exp_t * e);
  sl_space_t *sl_mk_form_pred (sl_context_t * ctx, sl_exp_t * e);
  sl_space_t *sl_exp_push_space (sl_context_t * ctx, sl_exp_t * e);
  void sl_exp_push (sl_context_t * ctx, sl_exp_t * e, int ispos);
/* Translates the expression into a formula and push in global formulas. */

#ifdef __cplusplus
}
#endif

#endif				/* _SL_H */
