/**************************************************************************
 *
 *  NOLL decision procedure
 *
 *  Copyright (C) 2012-2013
 *    LIAFA (University of Paris Diderot and CNRS)
 *
 *
 *  you can redistribute it and/or modify it under the terms of the GNU
 *  Lesser General Public License as published by the Free Software
 *  Foundation, version 3.
 *
 *  It is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  See the GNU Lesser General Public License version 3.
 *  for more details (enclosed in the file LICENSE).
 *
 **************************************************************************/

/** Additional definitions needed to parse NOLL files
 */

#ifndef _NOLL_H_
#define _NOLL_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
#include "noll_types.h"
#include "noll_vars.h"
#include "noll_preds.h"
#include "noll_form.h"
#include "noll_entl.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** AST built from the SMTLIB format.
 *  It is defined only for terms and formulas.
 */

/* Valid term builder in NOLL */
  typedef enum
  {
    NOLL_F_FALSE = 0,		/* boolean operators */
    NOLL_F_TRUE,
    NOLL_F_NOT,
    NOLL_F_AND,
    NOLL_F_OR,
    NOLL_F_IMPLIES,
    NOLL_F_EXISTS,
    NOLL_F_FORALL,
    NOLL_F_LVAR,		/* variable, field, or predicate */
    NOLL_F_SVAR,
    NOLL_F_FIELD,
    NOLL_F_PRED,
    NOLL_F_EQ,			/* pure operators */
    NOLL_F_DISTINCT,
    NOLL_F_EMP,			/* space operators */
    NOLL_F_JUNK,
    NOLL_F_WSEP,
    NOLL_F_SSEP,
    NOLL_F_PTO,
    NOLL_F_REF,
    NOLL_F_SREF,
    NOLL_F_INDEX,
    NOLL_F_SLOC,		/* share operators */
    NOLL_F_UNLOC,
    NOLL_F_INLOC,
    NOLL_F_NILOC,		/* not in */
    NOLL_F_EQLOC,
    NOLL_F_LELOC,
    NOLL_F_SELOC,
    NOLL_F_TOBOOL,
    NOLL_F_TOSPACE,
    NOLL_F_LOOP,		/* loop of length at least one */
    NOLL_F_OTHER
/* NOT TO BE USED */
  } noll_expkind_t;

  typedef struct noll_exp_t
  {
    noll_expkind_t discr;

    union
    {
      /* user-defined function or symbol name */
      uint_t sid;

      /* quantifiers */
      struct
      {
	/* reference to the array containing the variables quantified
	 * in a continuous region from [start to end) */
	noll_var_array *lvars;	/* location vars */
	uint_t lstart;		/* index starting the location quantified variables */
	uint_t lend;		/* index ending the location quantified variables */
	noll_var_array *svars;	/* set of location vars */
	uint_t sstart;		/* index starting the set of location quantified variables */
	uint_t send;		/* index ending the set of location quantified variables */
      } quant;
    } p;

    struct noll_exp_t **args;	/* array of expression args or NULL */
    uint_t size;		/* size of the array above */

  } noll_exp_t;

/* Context used to parse smtlib2 formulas */
  typedef struct noll_context_t
  {
    /* array storing the size of the frame of the stack
     * for location variables at each
     * quantifier level (only 3 levels are possible):
     * 0 -- size of globals,
     * 1 -- size of define-fun or exists in assert,
     * 2 -- exists in define-fun */
    noll_uint_array *lvar_stack;
    /* location variables environment */
    noll_var_array *lvar_env;

    /* array storing the size of the frame of the stack
     * for set of locations variables (only 2 levels are possible):
     * 0 -- size of globals,
     * 1 -- size of exists in assert */
    noll_uint_array *svar_stack;
    /* set of locations variables environment */
    noll_var_array *svar_env;

    /* predicate in definition */
    char *pname;
  } noll_context_t;

/**
 * Constants used for variables & parameters identifiers
 */
#define VID_NIL 0
#define VID_FST_PARAM 1
#define VID_SND_PARAM 2

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

  extern int noll_error_parsing;

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialize global variables */
  void noll_init (void);

/* Parsing context */
  noll_context_t *noll_mk_context (void);
  void noll_del_context (noll_context_t * ctx);
/* Allocator/deallocator. */
  void noll_pop_context (noll_context_t * ctx);
/* Pop the local variables. */

/* Parsing logic */
  int noll_set_logic (noll_context_t * ctx, const char *logic);

/* Functions */
  noll_type_t *noll_mk_fun_decl (noll_context_t * ctx, const char *name,
				 noll_type_t * ty);
/* Register a field or a variable. */
  uint_t noll_mk_fun_def (noll_context_t * ctx, const char *name, uint_t npar,
			  noll_type_t * rety, noll_exp_t * def);
/* Register a predicate definition. */

/* Commands */
  int noll_assert (noll_context_t * ctx, noll_exp_t * term);
  int noll_check (noll_context_t * ctx);

/* Terms */
  void noll_push_var (noll_context_t * ctx, const char *name,
		      noll_type_t * vty);
/* Declare a local variable in the context. */
  int noll_push_quant (noll_context_t * ctx);
  int noll_pop_quant (noll_context_t * ctx);
/* Increments/decrements the nesting of quantifiers. */

  noll_exp_t *noll_mk_exists (noll_context_t * ctx, noll_exp_t * term);
  noll_exp_t *noll_mk_app (noll_context_t * ctx, const char *name,
			   noll_exp_t ** args, uint_t size);
  noll_exp_t *noll_mk_symbol (noll_context_t * ctx, const char *name);
  noll_exp_t *noll_mk_pred (noll_context_t * ctx, const char *name,
			    noll_exp_t ** args, uint_t size);
  noll_exp_t *noll_mk_true (noll_context_t * ctx);
  noll_exp_t *noll_mk_false (noll_context_t * ctx);
  noll_exp_t *noll_mk_and (noll_context_t * ctx, noll_exp_t ** args,
			   uint_t size);
  noll_exp_t *noll_mk_or (noll_context_t * ctx, noll_exp_t ** args,
			  uint_t size);
  noll_exp_t *noll_mk_not (noll_context_t * ctx, noll_exp_t ** args,
			   uint_t size);
  noll_exp_t *noll_mk_eq (noll_context_t * ctx, noll_exp_t ** args,
			  uint_t size);
  noll_exp_t *noll_mk_distinct (noll_context_t * ctx, noll_exp_t ** args,
				uint_t size);
  noll_exp_t *noll_mk_emp (noll_context_t * ctx);
  noll_exp_t *noll_mk_junk (noll_context_t * ctx);
  noll_exp_t *noll_mk_wsep (noll_context_t * ctx, noll_exp_t ** args,
			    uint_t size);
  noll_exp_t *noll_mk_ssep (noll_context_t * ctx, noll_exp_t ** args,
			    uint_t size);
  noll_exp_t *noll_mk_pto (noll_context_t * ctx, noll_exp_t ** args,
			   uint_t size);
  noll_exp_t *noll_mk_ref (noll_context_t * ctx, noll_exp_t ** args,
			   uint_t size);
  noll_exp_t *noll_mk_sref (noll_context_t * ctx, noll_exp_t ** args,
			    uint_t size);
  noll_exp_t *noll_mk_index (noll_context_t * ctx, noll_exp_t ** args,
			     uint_t size);
  noll_exp_t *noll_mk_sloc (noll_context_t * ctx, noll_exp_t ** args,
			    uint_t size);
  noll_exp_t *noll_mk_unloc (noll_context_t * ctx, noll_exp_t ** args,
			     uint_t size);
  noll_exp_t *noll_mk_inloc (noll_context_t * ctx, noll_exp_t ** args,
			     uint_t size);
  noll_exp_t *noll_mk_eqloc (noll_context_t * ctx, noll_exp_t ** args,
			     uint_t size);
  noll_exp_t *noll_mk_leloc (noll_context_t * ctx, noll_exp_t ** args,
			     uint_t size);
  noll_exp_t *noll_mk_seloc (noll_context_t * ctx, noll_exp_t ** args,
			     uint_t size);
  noll_exp_t *noll_mk_tobool (noll_context_t * ctx, noll_exp_t ** args,
			      uint_t size);
  noll_exp_t *noll_mk_tospace (noll_context_t * ctx, noll_exp_t ** args,
			       uint_t size);
  noll_exp_t *noll_mk_loop (noll_context_t * ctx, noll_exp_t ** args,
			    uint_t size);

/* ====================================================================== */
/* Typechecking */
/* ====================================================================== */

  noll_exp_t *noll_exp_typecheck (noll_context_t * ctx, noll_exp_t * f);
/* Typecheck a formula and do some simplifications if needed. */

/* ====================================================================== */
/* Translation */
/* ====================================================================== */
/* Build a space formula from AST in args */
  void noll_exp_push_pure (noll_context_t * ctx, noll_exp_t * e,
			   noll_form_t * f);
  noll_space_t *noll_mk_form_junk (noll_exp_t * e);
  noll_space_t *noll_mk_form_pto (noll_context_t * ctx, noll_exp_t * e);
  noll_space_t *noll_mk_form_loop (noll_context_t * ctx, noll_exp_t * e);
  noll_space_t *noll_mk_form_pred (noll_context_t * ctx, noll_exp_t * e);
  noll_space_t *noll_exp_push_space (noll_context_t * ctx, noll_exp_t * e);
  void noll_exp_push (noll_context_t * ctx, noll_exp_t * e, int ispos);
/* Translates the expression into a formula and push in global formulas. */

/* ====================================================================== */
/* Handling errors */
/* ====================================================================== */

  void noll_error (int level, const char *fun, const char *msg);

#ifndef NDEBUG

#define NOLL_DEBUG(...) \
	do { \
			fprintf (stderr, __VA_ARGS__); \
	} while (0)

#else				/* #ifndef NDEBUG */

#define NOLL_DEBUG(...)		/* empty */

#endif				/* #ifndef NDEBUG */

#ifdef __cplusplus
}
#endif

#endif				/* _NOLL_H */
