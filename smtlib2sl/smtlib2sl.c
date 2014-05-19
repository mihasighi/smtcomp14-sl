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

#include <stdlib.h>
#include <string.h>
#include "smtlib2sl.h"

/**
 * Mapping of types from smtlib2abstractparser (file smtlib2types.h)
 * to types from SL parser (files sl.h and sl_types.h):
 * - smtlib2_sort (void*)  to     sl_type_t*
 * - smtlib2_term (void*)  to     sl_exp_t*
 */

/* =========================================================================
 * Forward declaration of
 * functions overriding the abstract parser functions.
 * ========================================================================= */

/* Commands */

static void smtlib2_sl_parser_set_logic (smtlib2_parser_interface * p,
					 const char *logic);
static void smtlib2_sl_parser_declare_sort (smtlib2_parser_interface * p,
					    const char *sortname, int arity);
static void smtlib2_sl_parser_declare_function (smtlib2_parser_interface *
						p, const char *name,
						smtlib2_sort sort);
static void smtlib2_sl_parser_define_function (smtlib2_parser_interface * p,
					       const char *name,
					       smtlib2_vector * params,
					       smtlib2_sort sort,
					       smtlib2_term term);
static void smtlib2_sl_parser_assert_formula (smtlib2_parser_interface * p,
					      smtlib2_term term);
static void smtlib2_sl_parser_check_sat (smtlib2_parser_interface * p);

/* Sorts */

static smtlib2_sort smtlib2_sl_parser_make_sort (smtlib2_parser_interface *
						 p, const char *sortname,
						 smtlib2_vector * index);
static smtlib2_sort
smtlib2_sl_parser_make_parametric_sort (smtlib2_parser_interface * p,
					const char *sortname,
					smtlib2_vector * tps);
static smtlib2_sort
smtlib2_sl_parser_make_function_sort (smtlib2_parser_interface * p,
				      smtlib2_vector * tps);

/* Terms */

static void smtlib2_sl_parser_declare_variable (smtlib2_parser_interface *
						parser, const char *name,
						smtlib2_sort sort);
static smtlib2_term
smtlib2_sl_parser_push_quantifier_scope (smtlib2_parser_interface * p);
static smtlib2_term
smtlib2_sl_parser_pop_quantifier_scope (smtlib2_parser_interface * p);
static smtlib2_term
smtlib2_sl_parser_make_forall_term (smtlib2_parser_interface * p,
				    smtlib2_term term);
static smtlib2_term
smtlib2_sl_parser_make_exists_term (smtlib2_parser_interface * p,
				    smtlib2_term term);
static smtlib2_term smtlib2_sl_parser_mk_function (smtlib2_context ctx,
						   const char *symbol,
						   smtlib2_sort sort,
						   smtlib2_vector * index,
						   smtlib2_vector * args);
#define SMTLIB2_SL_DECLHANDLER(name)				      \
    static smtlib2_term smtlib2_sl_parser_mk_ ## name (              \
        smtlib2_context ctx,                                            \
        const char *symbol,                                             \
        smtlib2_sort sort,                                              \
        smtlib2_vector *idx,                                            \
        smtlib2_vector *args)
SMTLIB2_SL_DECLHANDLER (and);
SMTLIB2_SL_DECLHANDLER (or);
SMTLIB2_SL_DECLHANDLER (not);
SMTLIB2_SL_DECLHANDLER (eq);
SMTLIB2_SL_DECLHANDLER (distinct);
//SMTLIB2_SL_DECLHANDLER (emp);
//SMTLIB2_SL_DECLHANDLER (junk);
SMTLIB2_SL_DECLHANDLER (ssep);
SMTLIB2_SL_DECLHANDLER (pto);
SMTLIB2_SL_DECLHANDLER (ref);
SMTLIB2_SL_DECLHANDLER (sref);
SMTLIB2_SL_DECLHANDLER (tobool);
SMTLIB2_SL_DECLHANDLER (tospace);
SMTLIB2_SL_DECLHANDLER (loop);

#define SMTLIB2_SL_SETHANDLER(tp, s, name) \
    smtlib2_term_parser_set_handler(tp, s, smtlib2_sl_parser_mk_ ## name)

/* =========================================================================
 * SL parser creation/destruction.
 * ========================================================================= */

#define sl_ctx(p) (((smtlib2_sl_parser *)(p))->ctx_)
#define sl_sorts(p) (((smtlib2_sl_parser *)(p))->sorts_)
#define sl_funs(p) (((smtlib2_sl_parser *)(p))->funs_)

smtlib2_sl_parser *
smtlib2_sl_parser_new (void)
{
  smtlib2_sl_parser *ret =
    (smtlib2_sl_parser *) malloc (sizeof (smtlib2_sl_parser));
  smtlib2_parser_interface *pi;
  smtlib2_term_parser *tp;
  smtlib2_abstract_parser *ap;

  ret->ctx_ = sl_mk_context ();
  smtlib2_abstract_parser_init ((smtlib2_abstract_parser *) ret,
				(smtlib2_context) ret);
  ret->sorts_ =
    smtlib2_hashtable_new (smtlib2_hashfun_str, smtlib2_eqfun_str);
  ret->funs_ = smtlib2_hashtable_new (smtlib2_hashfun_str, smtlib2_eqfun_str);

  /* initialize the parser interface and override virtual methods */
  pi = SMTLIB2_PARSER_INTERFACE (ret);
  /* Commands */
  pi->set_logic = smtlib2_sl_parser_set_logic;
  pi->declare_sort = smtlib2_sl_parser_declare_sort;
  pi->declare_function = smtlib2_sl_parser_declare_function;
  pi->define_function = smtlib2_sl_parser_define_function;
  pi->assert_formula = smtlib2_sl_parser_assert_formula;
  pi->check_sat = smtlib2_sl_parser_check_sat;
  /* Terms */
  pi->declare_variable = smtlib2_sl_parser_declare_variable;
  pi->push_quantifier_scope = smtlib2_sl_parser_push_quantifier_scope;
  pi->pop_quantifier_scope = smtlib2_sl_parser_pop_quantifier_scope;
  pi->make_forall_term = smtlib2_sl_parser_make_forall_term;
  pi->make_exists_term = smtlib2_sl_parser_make_exists_term;
  /* Sorts */
  pi->make_sort = smtlib2_sl_parser_make_sort;
  pi->make_parametric_sort = smtlib2_sl_parser_make_parametric_sort;
  pi->make_function_sort = smtlib2_sl_parser_make_function_sort;
  /* Term parser */
  tp = ((smtlib2_abstract_parser *) ret)->termparser_;
  /* for symbols and user-defined function application */
  smtlib2_term_parser_set_function_handler (tp,
					    smtlib2_sl_parser_mk_function);
  /* for logic pre-defined operators */
  SMTLIB2_SL_SETHANDLER (tp, "or", or);
  SMTLIB2_SL_SETHANDLER (tp, "and", and);
  SMTLIB2_SL_SETHANDLER (tp, "not", not);
  SMTLIB2_SL_SETHANDLER (tp, "=", eq);
  SMTLIB2_SL_SETHANDLER (tp, "distinct", distinct);
  SMTLIB2_SL_SETHANDLER (tp, "ssep", ssep);
  SMTLIB2_SL_SETHANDLER (tp, "pto", pto);
  SMTLIB2_SL_SETHANDLER (tp, "ref", ref);
  SMTLIB2_SL_SETHANDLER (tp, "sref", sref);
  SMTLIB2_SL_SETHANDLER (tp, "tobool", tobool);
  SMTLIB2_SL_SETHANDLER (tp, "tospace", tospace);
  SMTLIB2_SL_SETHANDLER (tp, "loop", loop);

  /* Initialize the logic pre-defined sorts */
  smtlib2_hashtable_set (ret->sorts_,
			 (intptr_t) (void *) smtlib2_strdup ("Bool"),
			 (intptr_t) (void *) sl_mk_type_bool ());
  smtlib2_hashtable_set (ret->sorts_,
			 (intptr_t) (void *) smtlib2_strdup ("Int"),
			 (intptr_t) (void *) sl_mk_type_int ());
  smtlib2_hashtable_set (ret->sorts_,
			 (intptr_t) (void *) smtlib2_strdup ("Field"),
			 (intptr_t) (void *) sl_mk_type_field (0, 0));
  smtlib2_hashtable_set (ret->sorts_,
			 (intptr_t) (void *) smtlib2_strdup ("SetLoc"),
			 (intptr_t) (void *) sl_mk_type_setloc ());
  smtlib2_hashtable_set (ret->sorts_,
			 (intptr_t) (void *) smtlib2_strdup ("SetRef"),
			 (intptr_t) (void *) sl_mk_type_setref (0));
  smtlib2_hashtable_set (ret->sorts_,
			 (intptr_t) (void *) smtlib2_strdup ("Space"),
			 (intptr_t) (void *) sl_mk_type_space ());

  /* set options in the abstract parser */
  ap = (smtlib2_abstract_parser *) pi;
  ap->print_success_ = false;

  return ret;
}

void
smtlib2_sl_parser_delete (smtlib2_sl_parser * p)
{
  smtlib2_hashtable_delete (sl_sorts (p), NULL, NULL);
  smtlib2_hashtable_delete (sl_funs (p), NULL, NULL);
  smtlib2_abstract_parser_deinit (&(p->parent_));
  sl_del_context (sl_ctx (p));
  free (p);
}

/* =========================================================================
 * Commands parsing.
 * ========================================================================= */

/**
 * Command (set-logic logic)
 * Only "QF_SL" is supported.
 */
static void
smtlib2_sl_parser_set_logic (smtlib2_parser_interface * p, const char *logic)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  /* fix logic only one time */
  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      /* check that the logic is supported, i.e., QF_SLRD or QF_SL */
      if (strcmp (logic, "QF_SL") > 0 && strcmp (logic, "QF_SLRD") > 0)
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ =
	    smtlib2_sprintf ("logic `%s' is not supported", logic);
	}
      /* if it is, declare primitive sorts */
      /* register the SetLoc sort */
      sl_type_t *ty = sl_mk_type_setloc ();
      smtlib2_hashtable_set (sl_sorts (p),
			     (intptr_t) (void *) smtlib2_strdup ("SetLoc"),
			     (intptr_t) (void *) ty);
    }
  else
    sl_error (0, "smtlib2parser_set_logic", "previous syntax error");
}

/** Command (declare-sort sortname arity).
 *  Used to declare record types; their arity shall be 0.
 */
static void
smtlib2_sl_parser_declare_sort (smtlib2_parser_interface * p,
				const char *sortname, int arity)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      intptr_t k;
      /* check that the sort is not already declared */
      if (smtlib2_hashtable_find (sl_sorts (p), (intptr_t) sortname, &k))
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ =
	    smtlib2_sprintf ("sort `%s' already declared or defined",
			     sortname);
	}
      else if (arity != 0)
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ =
	    smtlib2_sprintf ("sort declaration of arity != 0 not supported");
	}
      else
	{
	  /* register the record */
	  sl_type_t *ty = sl_record_register (sortname);
	  if (ty != NULL)
	    {
	      ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
	      smtlib2_hashtable_set (sl_sorts (p),
				     (intptr_t) (void *)
				     smtlib2_strdup (sortname),
				     (intptr_t) (void *) ty);
	    }
	  else
	    {
	      ap->response_ = SMTLIB2_RESPONSE_ERROR;
	      ap->errmsg_ =
		smtlib2_sprintf ("sort declaration `%s' not supported",
				 sortname);
	    }
	}
    }
  else
    sl_error (0, "smtlib2parser_declare_sort", "previous syntax error");
}

/** Command (declare-fun name args res)
 *  Used to declare SL fields and variables (location or set of locations).
 *  The args shall be empty.
 * @param name the name of the function declared
 * @param sort the res sort,
 *             already checked that args = () @see make_function_sort
 *
 */
static void
smtlib2_sl_parser_declare_function (smtlib2_parser_interface * p,
				    const char *name, smtlib2_sort sort)
{
  smtlib2_sl_parser *sp = (smtlib2_sl_parser *) p;
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      /* check that it is not already defined */
      intptr_t k;
      if (smtlib2_hashtable_find (sl_funs (p), (intptr_t) name, &k))
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_sprintf ("function `%s' already declared",
					 name);
	}
      else
	{
	  /* check that the function is supported */
	  sl_type_t *ty =
	    sl_mk_fun_decl (sl_ctx (p), name, (sl_type_t *) sort);
	  if (ty != NULL)
	    {
	      ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
	      smtlib2_hashtable_set (sp->funs_,
				     (intptr_t) (void *)
				     smtlib2_strdup (name),
				     (intptr_t) (void *) ty);
	    }
	  else
	    {
	      ap->response_ = SMTLIB2_RESPONSE_ERROR;
	      ap->errmsg_ =
		smtlib2_sprintf ("function declaration `%s' not supported",
				 name);
	    }
	}
    }
  else
    sl_error (0, "smtlib2parser_declare_fun", "previous syntax error");
}

/** Term (exists ...), (forall ...), (let ...), and
 *  function definition.
 *  Used to declare local variables.
 *  The variable declared is pushed in the local context.
 *
 *  @param name variable name; it shall start with ?
 *  @param sort variable type; it shall be a record
 */
static void
smtlib2_sl_parser_declare_variable (smtlib2_parser_interface * p,
				    const char *name, smtlib2_sort sort)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      sl_type_t *ty = (sl_type_t *) sort;
      if (ty != NULL)
	{
	  // variable declaration
	  // check that this name starts with  ?
	  if (name[0] != '?')
	    {
	      ap->response_ = SMTLIB2_RESPONSE_ERROR;
	      ap->errmsg_ =
		smtlib2_sprintf ("local variable `%s' is not a constant.",
				 name);
	    }
	  else if ((ty->kind != SL_TYP_RECORD) && (ty->kind != SL_TYP_SETLOC))
	    {
	      ap->response_ = SMTLIB2_RESPONSE_ERROR;
	      ap->errmsg_ =
		smtlib2_sprintf
		("local variable `%s' is not of primitive type.", name);
	    }
	  else
	    {
	      sl_push_var (sl_ctx (p), name, ty);
	    }
	}
    }
  else
    sl_error (0, "smtlib2parser_declare_var", "previous syntax error");
}

/** Command (define-fun name ( params ) sort term)
 *  Used to define predicates.
 *
 *  @param name  predicate name
 *  @param parms predicate arguments: a vector of terms;
 *               arguments already pushed in the local context;
 *               the @param term make reference to vars in the local context.
 *  @param sort  predicate return type
 *  @param term  predicate expression.
 *
 */
static void
smtlib2_sl_parser_define_function (smtlib2_parser_interface * p,
				   const char *name,
				   smtlib2_vector * params,
				   smtlib2_sort sort, smtlib2_term term)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  /* DO NOT apply the abstract parser function
   *    smtlib2_abstract_parser_define_function
   * because it adds term to termbinding_ and
   * this feature is not supported by the abstract parser for function call.
   */
  /* The following code is adapted from the abstract parser. */
  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      /* check that it is not already defined */
      intptr_t k;
      if (smtlib2_hashtable_find (sl_funs (p), (intptr_t) name, &k))
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ =
	    smtlib2_sprintf ("predicate or function `%s' already declared",
			     name);
	}
      else
	{
	  /* The name shall be bound to NULL. */
	  smtlib2_term_parser_define_binding (ap->termparser_, name, params,
					      NULL);
	  if (smtlib2_term_parser_error (ap->termparser_))
	    {
	      ap->response_ = SMTLIB2_RESPONSE_ERROR;
	      ap->errmsg_ =
		smtlib2_strdup (smtlib2_term_parser_get_error_msg
				(ap->termparser_));
	    }
	  else
	    {
	      /* register the predicate in the SL global array;
	       * the predicate name used for the recursive call is in the context
	       */
	      sl_context_t *ctx = sl_ctx (p);
	      size_t pid = sl_mk_fun_def (ctx, name,
					  smtlib2_vector_size (params),
					  (sl_type_t *) sort,
					  (sl_exp_t *) term);
	      if (pid == UNDEFINED_ID)
		{
		  ap->response_ = SMTLIB2_RESPONSE_ERROR;
		  ap->errmsg_ =
		    smtlib2_sprintf
		    ("predicate definition `%s' is not correct.", name);
		}
	      /* remove the local context */
	      sl_pop_context (ctx);
	    }
	}
    }
  else
    sl_error (0, "smtlib2parser_define_fun", "previous syntax error");
}

static void
smtlib2_sl_parser_assert_formula (smtlib2_parser_interface * p,
				  smtlib2_term term)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      // check also that assert has a good formula
      if (sl_assert (sl_ctx (p), (sl_exp_t *) term) == false)
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_strdup ("assert not a SL formula");
	}
    }
  else
    sl_error (0, "smtlib2parser_assert", "previous syntax error");
}

static void
smtlib2_sl_parser_check_sat (smtlib2_parser_interface * p)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      int s = sl_check (sl_ctx (p));
      // returns status of phi1 /\ not(phi2) 
      ap->response_ = SMTLIB2_RESPONSE_STATUS;
      switch (s)
	{
	case 1:
	  ap->status_ = SMTLIB2_STATUS_SAT;
	  break;
	case 0:
	  ap->status_ = SMTLIB2_STATUS_UNSAT;
	  break;
	default:
	  ap->status_ = SMTLIB2_STATUS_UNKNOWN;
	  break;
	}
    }
  else
    sl_error (0, "smtlib2parser_check_sat", "previous syntax error");
}

/* =========================================================================
 * Sorts parsing.
 * ========================================================================= */

/** Called for a sort use.
 */
static smtlib2_sort
smtlib2_sl_parser_make_sort (smtlib2_parser_interface * p,
			     const char *sortname, smtlib2_vector * index)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  sl_type_t *ret = NULL;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      intptr_t k;
      /* check that the sort is already declared */
      if (!smtlib2_hashtable_find (sl_sorts (p), (intptr_t) sortname, &k))
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_sprintf ("sort `%s' not declared", sortname);
	}
      else if (index != NULL)
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_sprintf ("unknown sort `%s' with index != 0",
					 sortname);
	}
      else
	ret = (sl_type_t *) k;
    }
  else
    sl_error (0, "smtlib2parser_make_sort", "previous syntax error");
  return (smtlib2_sort) ret;
}

/** Called in declare-fun to collect typing information.
 *
 * @param p abstract parser
 * @param tps vector of types for the args and result, will be deleted
 */
static smtlib2_sort
smtlib2_sl_parser_make_function_sort (smtlib2_parser_interface * p,
				      smtlib2_vector * tps)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  smtlib2_sort ret = NULL;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      /* shall be with 0 arguments */
      if (smtlib2_vector_size (tps) > 1)
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ =
	    smtlib2_sprintf ("make function with arity > 0 not supported");
	}
      // return the vector
      ret = (smtlib2_sort) smtlib2_vector_at (tps, 0);
    }
  else
    sl_error (0, "smtlib2parser_make_function_sort", "previous syntax error");
  return ret;
}

/** Called to instantiate Field parametric sort.
 * @param sortname name of the sort
 * @param tps      parameters used, their ids
 */
static smtlib2_sort
smtlib2_sl_parser_make_parametric_sort (smtlib2_parser_interface * p,
					const char *sortname,
					smtlib2_vector * tps)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  smtlib2_sort res = NULL;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      intptr_t k;
      /* check that the sort is already declared */
      if (!smtlib2_hashtable_find (sl_sorts (p), (intptr_t) sortname, &k))
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_sprintf ("sort `%s' not declared", sortname);
	}
      else
	{
	  /* check that the sort is exactly Field,
	   * since (SetRef sort) can not appear in the formula */
	  if (!strcmp (sortname, "Field") && tps && smtlib2_vector_size (tps)
	      == 2)
	    {
	      sl_type_t *src = (sl_type_t *) smtlib2_vector_at (tps, 0);
	      sl_type_t *dst = (sl_type_t *) smtlib2_vector_at (tps, 1);

	      if (src->kind == SL_TYP_RECORD && dst->kind == SL_TYP_RECORD)
		res =
		  (smtlib2_sort)
		  sl_mk_type_field (sl_vector_at (src->args, 0),
				    sl_vector_at (dst->args, 0));
	      else
		{
		  ap->response_ = SMTLIB2_RESPONSE_ERROR;
		  ap->errmsg_ = smtlib2_sprintf ("unsupported Field sort");
		}
	    }
	  else
	    {
	      ap->response_ = SMTLIB2_RESPONSE_ERROR;
	      ap->errmsg_ =
		smtlib2_sprintf ("unsupported parametric sort `%s'",
				 sortname);
	    }
	}
    }
  else
    sl_error (0, "smtlib2parser_make_parametric_sort",
	      "previous syntax error");
  return res;
}

/* =========================================================================
 * Terms parsing.
 * ========================================================================= */

/** Used in define-fun for parameters and quantified terms.
 *  Adds a level of nesting for quantifiers.
 *  For SL, only two levels are allowed in predicate definition.
 */
static smtlib2_term
smtlib2_sl_parser_push_quantifier_scope (smtlib2_parser_interface * p)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      if (!sl_push_quant (sl_ctx (p)))
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_strdup ("error in quantifiers");
	}
    }
  return NULL;
}

static smtlib2_term
smtlib2_sl_parser_pop_quantifier_scope (smtlib2_parser_interface * p)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      // pop all the local context, but do not free it, since used in predicates
      if (!sl_pop_quant (sl_ctx (p)))
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_strdup ("error in quantifiers");
	}
    }
  return NULL;
}

static smtlib2_term
smtlib2_sl_parser_make_forall_term (smtlib2_parser_interface * p,
				    smtlib2_term term)
{
  if (&term != &term)
    {
      assert (false);
    }

  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;
  smtlib2_term ret = NULL;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      ap->response_ = SMTLIB2_RESPONSE_ERROR;
      ap->errmsg_ = smtlib2_sprintf ("forall operator not supported");
    }
  else
    sl_error (0, "smtlib2parser_forall_term", "previous syntax error");
  return ret;
}

/** Used only in predicate definition.
 */
static smtlib2_term
smtlib2_sl_parser_make_exists_term (smtlib2_parser_interface * p,
				    smtlib2_term term)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *) p;
  sl_exp_t *res = NULL;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR)
    {
      res = sl_mk_exists (sl_ctx (p), (sl_exp_t *) term);
      if (!res)
	{
	  ap->response_ = SMTLIB2_RESPONSE_ERROR;
	  ap->errmsg_ = smtlib2_strdup ("error in quantifiers");
	}
    }
  else
    sl_error (0, "smtlib2parser_exists_term", "previous syntax error");
  return (smtlib2_term) res;
}

/** Used for function application term (symbol args).
 *
 * @param ctx    context of call
 * @param symbol name of the function
 * @param sort   type annotation NOT SUPPORTED
 * @param index  index annotation NOT SUPPORTED
 * @param args   arguments of call
 * @return term built with these arguments
 */
static smtlib2_term
smtlib2_sl_parser_mk_function (smtlib2_context ctx,
			       const char *symbol, smtlib2_sort sort,
			       smtlib2_vector * index, smtlib2_vector * args)
{
  if (&sort != &sort)
    {
      assert (false);
    }

  sl_context_t *sctx = sl_ctx (ctx);
  sl_exp_t *res = NULL;
  if (index)
    // indexed terms or as terms not supported
    return (smtlib2_term) NULL;
  if (args)
    // n-ary functions
    res = sl_mk_app (sctx, symbol,
		     (sl_exp_t **) (smtlib2_vector_array (args)),
		     smtlib2_vector_size (args));
  else
    // constant, variable or quantified variable
    res = sl_mk_app (sctx, symbol, NULL, 0);
  // no way to return a message using the context
  return (smtlib2_term) res;
}

SMTLIB2_SL_DECLHANDLER (and)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_and (sl_ctx (ctx),
		    (sl_exp_t **) (smtlib2_vector_array (args)),
		    smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (or)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_or (sl_ctx (ctx),
		   (sl_exp_t **) (smtlib2_vector_array (args)),
		   smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (not)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_not (sl_ctx (ctx),
		    (sl_exp_t **) (smtlib2_vector_array (args)),
		    smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (eq)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_eq (sl_ctx (ctx),
		   (sl_exp_t **) (smtlib2_vector_array (args)),
		   smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (distinct)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_distinct (sl_ctx (ctx),
			 (sl_exp_t **) (smtlib2_vector_array (args)),
			 smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (ssep)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_ssep (sl_ctx (ctx),
		     (sl_exp_t **) (smtlib2_vector_array (args)),
		     smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (pto)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_pto (sl_ctx (ctx),
		    (sl_exp_t **) (smtlib2_vector_array (args)),
		    smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (ref)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_ref (sl_ctx (ctx),
		    (sl_exp_t **) (smtlib2_vector_array (args)),
		    smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (sref)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_sref (sl_ctx (ctx),
		     (sl_exp_t **) (smtlib2_vector_array (args)),
		     smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (tobool)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_tobool (sl_ctx (ctx),
		       (sl_exp_t **) (smtlib2_vector_array (args)),
		       smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (tospace)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_tospace (sl_ctx (ctx),
			(sl_exp_t **) (smtlib2_vector_array (args)),
			smtlib2_vector_size (args));
}

SMTLIB2_SL_DECLHANDLER (loop)
{
  if (symbol != symbol && sort != sort && idx != idx)
    {
      assert (0);		// to remove warnings in unsed parameters
    }
  return sl_mk_loop (sl_ctx (ctx),
		     (sl_exp_t **) (smtlib2_vector_array (args)),
		     smtlib2_vector_size (args));
}
