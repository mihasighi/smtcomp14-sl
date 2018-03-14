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

#include "sl_util.h"
#include "sl.h"

/*
 * ======================================================================
 * Globals
 * ======================================================================
 */

void
sl_init ()
{
  sl_record_init ();
  sl_field_init ();
  sl_pred_init ();
  sl_prob_init ();
}

/*
 * ======================================================================
 * Context
 * ======================================================================
 */

sl_context_t *
sl_mk_context (void)
{
  sl_context_t *r = (sl_context_t *) malloc (sizeof (struct sl_context_t));

  /* initialize the global tables for the analysis */
  sl_init ();

#ifndef NDEBUG
  printf ("sl_mk_context reset qstack\n");
#endif
  /* initialize the stack of location variables to store
   * one global variable (nil) */
  r->lvar_stack = sl_uint_array_new ();
  sl_uint_array_push (r->lvar_stack, 1);

  /* initialize the set of location variables to store
   * nil */
  r->lvar_env = sl_var_array_new ();
  sl_var_register (r->lvar_env, "nil",
		   sl_record_find ("void"), SL_SCOPE_GLOBAL);

  /* the current procedure name */
  r->pname = NULL;

  return r;
}

/**
 * Destroy context data at the end of parsing.
 */
void
sl_del_context (sl_context_t * ctx)
{
  //ctx->l_env is in general in use
  sl_uint_array_delete (ctx->lvar_stack);
  sl_var_array_delete (ctx->lvar_env);
  free (ctx->pname);
  //not in use, usually
  free (ctx);
}

/**
 * Unlink context variables at the end of define-fun.
 * It is called before sl_pop_quant
 */
void
sl_pop_context (sl_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "sl_pop_context start\n");
  fflush (stdout);
#endif
  /*
   * the entries for exists and parameters will be deleted after that
   * by sl_pop_quant no global variables added
   */
  assert (sl_vector_at (ctx->lvar_stack, 0) == 1);
  /* the location array is reused in the function, 
   * thus only forget it and reenter "nil"
   */
  ctx->lvar_env = sl_var_array_new ();
  sl_var_register (ctx->lvar_env, "nil",
		   sl_record_find ("void"), SL_SCOPE_GLOBAL);
  /* unset the predicate name is allocated */
  ctx->pname = NULL;
}

/**
 * Reinitialize the context to globals.
 * A new array shall be created for the @p ctx->*vars.
 */
void
sl_contex_restore_global (sl_context_t * ctx)
{
  assert (ctx != NULL);
  assert (ctx->lvar_env != NULL);
  assert (ctx->lvar_stack != NULL);

#ifndef NDEBUG
  fprintf (stderr, "sl_context_restore_global: (begin) %d vars\n",
	   sl_vector_at (ctx->lvar_stack, 0));
#endif
  // ctx->* vars have been copied in  the formulae
  // refill the context with the global variables
  sl_var_array *arr = ctx->lvar_env;
  //this array is in the formulae
  uint_t size = sl_vector_at (ctx->lvar_stack, 0);
  ctx->lvar_env = sl_var_array_new ();
  if (size > 0)
    sl_var_array_reserve (ctx->lvar_env, size);
  for (uint_t i = 0; i < size; i++)
    sl_var_array_push (ctx->lvar_env, sl_var_copy (sl_vector_at (arr, i)));

#ifndef NDEBUG
  fprintf (stderr, "sl_context_restore_global: (end) %d vars\n",
	   sl_vector_size (ctx->lvar_env));
#endif
  return;
}

void
sl_context_fprint (FILE * f, sl_context_t * ctx)
{
  if (ctx == NULL)
    {
      fprintf (f, "ctx = NULL\n");
      return;
    }
  fprintf (f, "ctx = [pname => %s,\n", ctx->pname);

  fprintf (f, "\tlvar_stack => [");
  if (ctx->lvar_stack == NULL)
    fprintf (f, "NULL");
  else
    {
      for (uint_t i = 0; i < sl_vector_size (ctx->lvar_stack); i++)
	fprintf (stdout, "%d,", sl_vector_at (ctx->lvar_stack, i));
    }
  fprintf (stdout, "\n\t]\n");

  fprintf (f, "\tlvar_env => ");
  if (ctx->lvar_env == NULL)
    fprintf (f, "NULL");
  else
    fprintf (f, "%d", sl_vector_size (ctx->lvar_env));

  fprintf (stdout, "\n]\n");
}

/*
 * ======================================================================
 * Logic
 * ======================================================================
 */

/** Checks that the logic is supported.
 * @return 1 if the logic is correct, 0 otherwise
 */
int
sl_set_logic (sl_context_t * ctx, const char *logic)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (!strcmp (logic, "QF_S"))
    {
      sl_error (0, "set-logic", "unknown logic");
      return 0;
    }
  return 1;
}

/*
 * ======================================================================
 * Commands
 * ======================================================================
 */

/**
 * Declare a variable or a field.
 * @pre: The @p name is not yet used or predefined.
 * @param ctx    context of the declaration, only globals
 * @param name   identifier declared
 * @param rty    (optionnal) record type
 * @return       @p rty if correct declaration, NULL otherwise 
 */
sl_type_t *
sl_mk_fun_decl (sl_context_t * ctx, const char *name, sl_type_t * rty)
{
  switch (rty->kind)
    {
    case SL_TYP_RECORD:
      {
	/* global variable declaration
	 * register it in the array of variables
	 */
	sl_var_register (ctx->lvar_env, name, rty, SL_SCOPE_GLOBAL);
	if (rty != NULL)
	  sl_vector_at (ctx->lvar_stack, 0) += 1;
	return rty;
      }
    case SL_TYP_FIELD:
      {
	//field declaration
	// register it in the array of fields
	sl_field_register (name, rty);
	return rty;
      }
    default:
      //error, return NULL below
      break;
    }
  return NULL;
}

/**
 * Push the case included in @param e into @param pcases.
 * Assume: e is a boolean (existential or pure) and space formula.
 */
uint_t
sl_mk_fun_case (sl_context_t * ctx, const char *name, sl_pred_case_t * pcase,
		sl_exp_t * e)
{
  assert (NULL != ctx);
  assert (NULL != name);
  assert (NULL != pcase);
  assert (NULL != e);

  switch (e->discr)
    {
    case SL_F_EXISTS:
      {
	/*
	 * Notice: qarr == ctx->l_env[npar,...] and npar == e->p.quant.start
	 */
	sl_var_array *qarr = e->p.quant.lvars;
	/* check the starting index of existentially quantified vars */
	if ((qarr == NULL) || ((pcase->argc + 1) != e->p.quant.lstart))
	  {
	    sl_error (1, "Building predicate definition ", name);
	    sl_error (1, "Exists without variables ", "(or internal error)");
	    return 0;
	  }
	// push local vars into case
	pcase->lvars = qarr;
	return sl_mk_fun_case (ctx, name, pcase, e->args[0]);
      }

    case SL_F_AND:		/* if pure and space */
    case SL_F_TOBOOL:		/* then space */
    case SL_F_SSEP:
      {
	// add formula to the case
	for (size_t i = 0; i < e->size; i++)
	  {
	    uint_t ret = sl_mk_fun_case (ctx, name, pcase, e->args[i]);
	    if (ret == 0)
	      return 0;
	  }
	break;
      }

    case SL_F_DISTINCT:
    case SL_F_EQ:		/* pure formula */
      {
	assert (NULL != pcase->pure);
	sl_exp_push_pure (ctx, e, pcase->pure);
	break;
      }

    case SL_F_EMP:
      {				// nothing
	break;
      }
    case SL_F_JUNK:
      {
	pcase->is_precise = false;
	break;
      }
    case SL_F_PTO:
      {
	sl_space_t *pto = sl_mk_form_pto (ctx, e);
	assert (NULL != pcase->space);
	sl_space_array_push (pcase->space, pto);
	break;
      }
    case SL_F_LOOP:
      {
	/* before the non-recursive call of a predicate */
	if (e->size != 1 || e->args[0]->discr != SL_F_PRED)
	  {
	    sl_error (1, "Building predicate definition ", name);
	    sl_error (1, "Incorrect loop space formula ",
		      "(argument not a predicate call)");
	    return 0;
	  }
	else
	  {
	    sl_exp_t *fpred = e->args[0];
	    /* shall not be a recursive call */
	    if (fpred->p.sid == UNDEFINED_ID)
	      {
		sl_error (1, "Building predicate definition ", name);
		sl_error (1, "Incorrect loop space formula ",
			  "(argument a recursive predicate call)");
		return 0;
	      }
	    else
	      {
		sl_space_t *loop = sl_mk_form_loop (ctx, e);
		assert (NULL != pcase->space);
		sl_space_array_push (pcase->space, loop);
	      }
	  }
	break;
      }
    case SL_F_PRED:
      {
	/* predicate call */
	sl_space_t *pcall = sl_mk_form_pred (ctx, e);
	assert (NULL != pcase->space);
	sl_space_array_push (pcase->space, pcall);
	break;
      }
    default:
      break;
    }				//end switch

  return 1;
}

/**
 * Define a predicate.
 *
 * @param ctx   contains the parameters and local variables
 * @param name  name of the predicate
 * @param npar  number of parameters in the local context, first npar
 * @param rety  return type (shall be Space)
 * @param def   the term defining the predicate
 * @return      the identifier of the predicate defined or UNDEFINED_ID
 */
uint_t
sl_mk_fun_def (sl_context_t * ctx, const char *name, uint_t npar,
	       sl_type_t * rety, sl_exp_t * def)
{
  /* Warning: modified to allow general recursive definitions */
  /* the predicate may be already included in the preds_array
   * by a forward use */
  uid_t pid = sl_pred_register (name, NULL);
  // set the initial predicate if not done
  sl_prob_set_pid(pid);

  if (ctx->pname != NULL && strcmp (ctx->pname, name))
    {
      /* name does not correspond to this predicate definition */
      sl_error (1, "Building predicate definition ", name);
      sl_error (1, "Incorrect predicate name in ", name);
      return UNDEFINED_ID;
    }
  /*
   * assert: no global variables except the "nil" constant
   * may be defined before the predicate definition,
   * since no global context is kept for the definition of
   * the predicate
   */
  if (sl_vector_at (ctx->lvar_stack, 0) >= 2)
    {
      sl_error (1, "Building predicate definition ", name);
      sl_error (1, "Global variables declared before ", name);
      return UNDEFINED_ID;
    }
  /*
   * assert: number of parameters is at least 1 and
   * exactly the ctx->lvar_stack[1]
   */
  if (sl_vector_size (ctx->lvar_env) < 1)
    {
      sl_error (1, "Building predicate definition ", name);
      sl_error (1, "Empty set of parameters in ", name);
      return UNDEFINED_ID;
    }
  if (sl_vector_at (ctx->lvar_stack, 1) < 1)
    {
      sl_error (1, "Building predicate definition ", name);
      sl_error (1, "Incorrect number of parameters (< 1) in ", name);
      return UNDEFINED_ID;
    }
  if ((sl_vector_at (ctx->lvar_stack, 1) > sl_vector_size (ctx->lvar_env))
      || (sl_vector_at (ctx->lvar_stack, 1) != npar))
    {
      sl_error (1, "Building predicate definition ", name);
      sl_error (1, "Incorrect number of parameters in ", name);
      return UNDEFINED_ID;
    }
  /* assert:rety sort shall be Space */
  if ((rety == NULL) || (rety->kind != SL_TYP_SPACE))
    {
      sl_error (1, "Building predicate definition ", name);
      sl_error (1, "Incorrect result type (!= Space) ", name);
      return UNDEFINED_ID;
    }
  /*
   * Check the syntax of predicates while
   * the predicate definition is built
   */
  /* cond 0: all the parameters are of record type */
  for (uint_t i = 1; i <= npar; i++)
    {
      if (sl_var_record (ctx->lvar_env, i) == UNDEFINED_ID)
	{
	  sl_error (1, "Building predicate definition ", name);
	  sl_error (1, "Parameter not of record type ", name);
	  return UNDEFINED_ID;
	}
    }

  /* cond 1: the def has the form (tospace( ...)) or 
   *         directly a space formula 
   * Build list of cases */
  sl_exp_t *fcases = def;
  sl_pred_case_array *pcases = sl_pred_case_array_new ();
  if (def->discr == SL_F_TOSPACE)
    fcases = def->args[0];
  if (fcases->discr == SL_F_OR)
    {
      /* Warning: only OR at top most level */
      // several cases
      for (size_t i = 0; i < fcases->size; i++)
	{
	  // start a new predicate case
	  sl_pred_case_t *pcase = sl_pred_case_new (npar);
	  uint_t ret = sl_mk_fun_case (ctx, name, pcase, fcases->args[i]);
	  if (ret == 0)
	    return UNDEFINED_ID;	// TODO: free pcases
	  sl_pred_case_array_add (pcases, pcase);
	}
    }
  else
    {
      // start a new predicate case
      sl_pred_case_t *pcase = sl_pred_case_new (npar);
      uint_t ret = sl_mk_fun_case (ctx, name, pcase, fcases);
      if (ret == 0)
	return UNDEFINED_ID;	// TODO: free pcases
      sl_pred_case_array_add (pcases, pcase);
    }

  /*
   * build the record for this predicate definition and register it
   */
  sl_pred_binding_t *pdef =
    (sl_pred_binding_t *) malloc (sizeof (sl_pred_binding_t));
  pdef->pargs = 0;
  pdef->argc = npar;
  pdef->args = ctx->lvar_env;
  pdef->cases = pcases;

  /* restore the global environment */
  sl_contex_restore_global (ctx);

  /* register the  predicate */
  return sl_pred_register (name, pdef);
}

int
sl_assert (sl_context_t * ctx, sl_exp_t * term)
{
  //check that the formula is not null
  if (!term)
    {
      sl_error (1, "sl_assert", "null formula");
      return 0;
    }
  /* if the local environment is not empty, signal it */
  if (sl_vector_size (ctx->lvar_stack) > 1)
    {
      sl_error (1, "sl_assert", "non empty local environment");
      return 0;
    }
  /* typecheck the formula and do simplifications, if needed */
  sl_exp_t *form = sl_exp_typecheck (ctx, term);
  if (form == NULL)
    {
      sl_error (1, "sl_assert", "typechecking error");
      return 0;
    }
  /* translate into a formula and
   * fill the positive or negative formulae depending on the first operator
   */
  if (form->discr == SL_F_NOT)
    sl_exp_push (ctx, form->args[0], 0);
  /* push in negative */
  else
    sl_exp_push (ctx, form, 1);
  /* push in positive */

  /* restore the global environment */
  sl_contex_restore_global (ctx);

  return 1;
}

/**
 * Sets the command.
 */
int
sl_check (sl_context_t * ctx)
{
  if (sl_error_parsing > 0)
    {
      //assert (sl_prob->smt_fname != NULL);
      sl_error (0, "sl_check", "stop check because of parsing error");
      return 0;
    }

  sl_prob_set_cmd (SL_PROB_SAT);

#ifndef NDEBUG
  sl_prob_fprint (stdout);
#endif

  return 1;
}

/*
 * ======================================================================
 * Terms
 * ======================================================================
 */

/** Adds the variable to the topmost local array in the context,
 * depending of this type.
 */
void
sl_push_var (sl_context_t * ctx, const char *name, sl_type_t * vty)
{
  if (!ctx)
    return;

  uid_t vid = UNDEFINED_ID;
  if (vty->kind == SL_TYP_RECORD)
    {
      assert (ctx->lvar_env != NULL);
      sl_var_t *v = sl_var_new (name, vty, SL_SCOPE_LOCAL);
      sl_var_array_push (ctx->lvar_env, v);
      v->vid = sl_vector_size (ctx->lvar_env) - 1;
      //update the number of elements in the top of the stack
      uint_t top_stack = sl_vector_size (ctx->lvar_stack) - 1;
      sl_vector_at (ctx->lvar_stack, top_stack) += 1;
    }
  else
    assert (0);
}

int
sl_push_quant (sl_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "push_quant start: ");
  sl_context_fprint (stdout, ctx);
#endif
  //the SL supports only 2 levels of nesting and only inside define - fun
  if (sl_vector_size (ctx->lvar_stack) >= 3)
    {
      sl_error (0, "sl_push_quant", "too much nesting");
      return 0;
    }
  sl_uint_array_push (ctx->lvar_stack, 0);
  return 1;
}

int
sl_pop_quant (sl_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "pop_quant start: ");
  sl_context_fprint (stdout, ctx);
#endif
  if (sl_vector_size (ctx->lvar_stack) <= 1)
    {
      sl_error (0, "sl_pop_quant", "too much pops");
      return 0;
    }
  // for existential quantifiers,
  // pops vars in ctx->lvar_env on last(ctx->lvar_stack)
  if (sl_vector_size (ctx->lvar_stack) == 3)
    {
      uint_t nb_exists = sl_vector_last (ctx->lvar_stack);
      for (uint_t i = 0; i < nb_exists; i++)
	sl_var_array_pop (ctx->lvar_env);
    }
  sl_uint_array_pop (ctx->lvar_stack);
  return 1;
}

sl_exp_t *
sl_mk_op (sl_expkind_t f, sl_exp_t ** args, uint_t size)
{
  uint_t i;
  sl_exp_t *res = (sl_exp_t *) malloc (sizeof (struct sl_exp_t));
  res->discr = f;
  res->size = size;
  res->args = NULL;
  if (size)
    {
      res->args = (sl_exp_t **) malloc (size * sizeof (sl_exp_t *));
      for (i = 0; i < size; i++)
	res->args[i] = args[i];
    }
  return res;
}

/**
 * This function is called
 * - either for predicate definition
 * - either at the top-most of a SL formula
 */
sl_exp_t *
sl_mk_exists (sl_context_t * ctx, sl_exp_t * term)
{
  //the exist variables are at the end of the stack,
  //i.e., top of ctx->* var_stack element,
  //in ctx->* _env

  uint_t nb_exists_lvar = sl_vector_last (ctx->lvar_stack);

#ifndef NDEBUG
  fprintf (stdout, "mk_exists start lvar_stack=[");
  for (uint_t i = 0; i < sl_vector_size (ctx->lvar_stack); i++)
    fprintf (stdout, "%d,", sl_vector_at (ctx->lvar_stack, i));
  fprintf (stdout, "]\n");
  fprintf (stdout, "mk_exists exists lvar=[");
  for (uint_t i = nb_exists_lvar; i > 0; i--)
    {
      sl_var_t *vi = sl_vector_at (ctx->lvar_env,
				   sl_vector_size (ctx->lvar_env) - i);
      fprintf (stdout, "%s,", vi->vname);
    }
  fprintf (stdout, "]\n");
#endif
  sl_exp_t *res = sl_mk_op (SL_F_EXISTS, &term, 1);
  res->p.quant.lvars = sl_var_array_new ();
  sl_var_array_reserve (res->p.quant.lvars, nb_exists_lvar);
  res->p.quant.lstart = sl_vector_size (ctx->lvar_env) - nb_exists_lvar;
  res->p.quant.lend = sl_vector_size (ctx->lvar_env);
  for (uint_t i = 0, j = res->p.quant.lstart; i < nb_exists_lvar; i++, j++)
    sl_var_array_push (res->p.quant.lvars, sl_vector_at (ctx->lvar_env, j));

  return res;
}

/** Used to build terms from user-defined predicates
 *  or symbols (variables or fields) or true/false.
 * @param ctx contains the local context
 * @param name function name
 * @param args array of size of arguments
 * @param size length of the array above
 * @return the term built
 */
sl_exp_t *
sl_mk_app (sl_context_t * ctx, const char *name, sl_exp_t ** args,
	   uint_t size)
{
  if (size == 0)
    {
      //is null - ary symbols(true, false, emp, junk) or variable
      if (strcmp (name, "true") == 0)
	return sl_mk_true (ctx);
      if (strcmp (name, "false") == 0)
	return sl_mk_false (ctx);
      if (strcmp (name, "emp") == 0)
	return sl_mk_emp (ctx);
      if (strcmp (name, "junk") == 0)
	return sl_mk_junk (ctx);
      return sl_mk_symbol (ctx, name);
    }
  //is a predicate call(name args)
  return sl_mk_pred (ctx, name, args, size);
}

/** Build a term from this variable or field.
 */
sl_exp_t *
sl_mk_symbol (sl_context_t * ctx, const char *name)
{
  assert (ctx && name);
  sl_exp_t *ret = NULL;
  uint_t sid = UNDEFINED_ID;
  sl_type_t *typ = NULL;
#ifndef NDEBUG
  fprintf (stdout, "mk_symbol: start %s\n", name);
  fflush (stdout);
#endif
  /* special case of 'nil'?
     if (strcmp (name, "nil") == 0)
     {
     ret = sl_mk_op (SL_F_LVAR, NULL, 0);
     ret->p.sid = VNIL_ID;
     return ret;
     }
   */
  //search the variable environment
  // -search in the location env
  assert (ctx->lvar_env != NULL);
  sid = sl_var_array_find_local (ctx->lvar_env, name);
  if (sid != UNDEFINED_ID)
    typ = (sl_vector_at (ctx->lvar_env, sid))->vty;
  else
    typ = NULL;
  if (typ != NULL)
    {
      if (typ->kind == SL_TYP_RECORD)
	{
	  ret = sl_mk_op (SL_F_LVAR, NULL, 0);
	  ret->p.sid = sid;
	}
      else
	assert (0);
#ifndef NDEBUG
      fprintf (stdout, "mk_symbol: local %s (id %d)\n", name, ret->p.sid);
#endif
      return ret;
    }
  /* else, it shall be a field */
  if (name[0] == '?')
    {
      //fields cannot start with ?
      sl_error_id (1, "sl_mk_symbol", name);
      return NULL;
    }
  sid = sl_field_array_find (name);
  if (sid != UNDEFINED_ID)
    {
      ret = sl_mk_op (SL_F_FIELD, NULL, 0);
      ret->p.sid = sid;
      return ret;
    }
  /* else error */
  sl_error_id (1, "sl_mk_symbol", name);
  return NULL;
}

sl_exp_t *
sl_mk_pred (sl_context_t * ctx, const char *name, sl_exp_t ** args,
	    uint_t size)
{
  assert (ctx != NULL);
  assert (name != NULL);
  assert (args != NULL);
  if ((ctx == ctx) && /* To avoid silly warning */
      (size < 1))
    {
      char *msg = strdup (name);
      sl_error_args (1, msg, size, ">= 1");
      free (msg);
      return NULL;
    }
  //search the predicate name
  uint_t pid = sl_pred_array_find (name);
  if (pid == UNDEFINED_ID)
    {
      SL_DEBUG ("sl_mk_pred: %s, return UNDEF!\n", name);
      // forward use of a predicate
      pid = sl_pred_register (name, NULL);
    }
  //typechecking is done afterwards, build the expression
  sl_exp_t *res = sl_mk_op (SL_F_PRED, args, size);
  res->p.sid = pid;
  return res;
}

sl_exp_t *
sl_mk_true (sl_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  sl_exp_t *res = (sl_exp_t *) malloc (sizeof (struct sl_exp_t));
  res->discr = SL_F_TRUE;
  return res;
}

sl_exp_t *
sl_mk_false (sl_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  sl_exp_t *res = (sl_exp_t *) malloc (sizeof (struct sl_exp_t));
  res->discr = SL_F_FALSE;
  return res;
}

sl_exp_t *
sl_mk_and (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (size <= 0)
    /*
     * 0 arguments is
     * false
     */
    return sl_mk_false (ctx);
  else if (size == 1)
    return args[0];
  return sl_mk_op (SL_F_AND, args, size);
}

sl_exp_t *
sl_mk_or (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (size <= 0)
    /*
     * 0 arguments is
     * true
     */
    return sl_mk_true (ctx);
  else if (size == 1)
    return args[0];
  return sl_mk_op (SL_F_OR, args, size);
}

sl_exp_t *
sl_mk_not (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    sl_error_args (1, "sl_mk_not", size, "= 1");
  return sl_mk_op (SL_F_NOT, args, size);
}

sl_exp_t *
sl_mk_eq (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    sl_error_args (1, "sl_mk_eq", size, "= 2");
  return sl_mk_op (SL_F_EQ, args, size);
}

sl_exp_t *
sl_mk_distinct (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    sl_error_args (1, "sl_mk_distinct", size, "= 2");
  return sl_mk_op (SL_F_DISTINCT, args, size);
}

sl_exp_t *
sl_mk_emp (sl_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  sl_exp_t *res = (sl_exp_t *) malloc (sizeof (struct sl_exp_t));
  res->discr = SL_F_EMP;
  return res;
}

sl_exp_t *
sl_mk_junk (sl_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  sl_exp_t *res = (sl_exp_t *) malloc (sizeof (struct sl_exp_t));
  res->discr = SL_F_JUNK;
  return res;
}

sl_exp_t *
sl_mk_ssep (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    sl_error_args (1, "sl_mk_ssep", size, ">= 2");
  return sl_mk_op (SL_F_SSEP, args, size);
}

sl_exp_t *
sl_mk_pto (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    sl_error_args (1, "sl_mk_pto", size, "= 2");
  return sl_mk_op (SL_F_PTO, args, size);
}

sl_exp_t *
sl_mk_ref (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    sl_error_args (1, "sl_mksref", size, ">= 2");
  return sl_mk_op (SL_F_REF, args, size);
}

sl_exp_t *
sl_mk_sref (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    sl_error_args (1, "sl_mk_sref", size, ">= 2");
  return sl_mk_op (SL_F_SREF, args, size);
}

sl_exp_t *
sl_mk_tobool (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    sl_error_args (1, "sl_mk_tobool", size, "= 1");
  return sl_mk_op (SL_F_TOBOOL, args, size);
}

sl_exp_t *
sl_mk_tospace (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    sl_error_args (1, "sl_mk_tospace", size, "= 1");
  return sl_mk_op (SL_F_TOSPACE, args, size);
}

sl_exp_t *
sl_mk_loop (sl_context_t * ctx, sl_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    sl_error_args (1, "sl_mk_loop", size, "= 1");
  return sl_mk_op (SL_F_LOOP, args, size);
}

/*
 * ======================================================================
 * Printing
 * ======================================================================
 */

void
sl_exp_printf (FILE * f, sl_context_t * ctx, sl_exp_t * e)
{
  assert (f);
  if (!e)
    {
      fprintf (f, "null\n");
      return;
    }
  switch (e->discr)
    {
    case SL_F_FALSE:
      {
	fprintf (f, " false ");
	return;
      }
    case SL_F_TRUE:
      {
	fprintf (f, " true ");
	return;
      }
    case SL_F_LVAR:
      {
	fprintf (f, " %s ",
		 sl_var_name (ctx->lvar_env, e->p.sid, SL_TYP_RECORD));
	return;
      }
    case SL_F_FIELD:
      {
	fprintf (f, " %s ", sl_field_name (e->p.sid));
	return;
      }
    case SL_F_EMP:
      {
	fprintf (f, " emp ");
	return;
      }
    case SL_F_JUNK:
      {
	fprintf (f, " junk ");
	return;
      }
    case SL_F_NOT:
      {
	fprintf (f, " (not \n");
	break;
      }
    case SL_F_AND:
      {
	fprintf (f, " (and \n\t");
	break;
      }
    case SL_F_OR:
      {
	fprintf (f, " (or \n\t");
	break;
      }
    case SL_F_IMPLIES:
      {
	fprintf (f, " (implies \n\t");
	break;
      }
    case SL_F_EXISTS:
      {
	fprintf (f, " (exists (");
	for (uint_t i = e->p.quant.lstart; i < e->p.quant.lend; i++)
	  {
	    sl_var_t *vi =
	      sl_vector_at (e->p.quant.lvars, i - e->p.quant.lstart);
	    fprintf (f, " (%s %s) ", vi->vname,
		     sl_record_name (sl_var_record
				     (e->p.quant.lvars,
				      i - e->p.quant.lstart)));
	  }
	fprintf (f, " )\n\t");
	break;
      }
    case SL_F_PRED:
      {
	const char *pred_name = sl_pred_name (e->p.sid);
	assert (NULL != pred_name);
	fprintf (f, " (%s ", pred_name);
	break;
      }
    case SL_F_EQ:
      {
	fprintf (f, " (= ");
	break;
      }
    case SL_F_DISTINCT:
      {
	fprintf (f, " (distinct ");
	break;
      }
    case SL_F_SSEP:
      {
	fprintf (f, " (ssep \n\t");
	break;
      }
    case SL_F_PTO:
      {
	fprintf (f, " (pto ");
	break;
      }
    case SL_F_REF:
      {
	fprintf (f, " (ref ");
	break;
      }
    case SL_F_SREF:
      {
	fprintf (f, " (sref \n\t");
	break;
      }
    case SL_F_TOBOOL:
      {
	fprintf (f, " (tobool \n\t");
	break;
      }
    case SL_F_TOSPACE:
      {
	fprintf (f, " (tospace \n\t");
	break;
      }
    case SL_F_LOOP:
      {
	fprintf (f, " (loop \n\t");
	break;
      }
    default:
      {
	fprintf (f, " (unknown \n\t");
	break;
      }
    }
  if (e->args)
    {
      uint_t i;
      for (i = 0; i < e->size; i++)
	{
	  sl_exp_printf (f, ctx, e->args[i]);
	  fprintf (f, "\n\t");
	}
    }
  fprintf (f, " )\n");
}

/*
 * ======================================================================
 * Typechecking
 * ======================================================================
 */

/**
 * Typechecks an AND formula in the local environment env.
 */
sl_exp_t *
sl_exp_typecheck_and (sl_context_t * ctx, sl_exp_t * e)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (!e)
    return e;

  //top formulas shall be linked by and or tobool, expected type bool
  assert ((e->discr == SL_F_AND) || (e->discr == SL_F_TOBOOL));
  //TODO
  return e;
}

/**
 * Typechecks an EXISTS formula.
 */
sl_exp_t *
sl_exp_typecheck_exists (sl_context_t * ctx, sl_exp_t * e)
{
  if (!e)
    return e;
  if (e->discr == SL_F_EXISTS)
    {
      //top formula shall non be empty, expected type bool
      assert (e->size == 1);
      e->args[0] = sl_exp_typecheck_and (ctx, e->args[0]);
      if (!e->args[0])
	return NULL;
      return e;
    }
  return sl_exp_typecheck_and (ctx, e);
}

/** Typechecks the expression and simplifies it.
 *  Expected type is boolean at the top level.
 * @param ctx  context with global variables
 * @param e    formula to be typechecked
 * @return the new (simplified) formula
 */
sl_exp_t *
sl_exp_typecheck (sl_context_t * ctx, sl_exp_t * e)
{
  if (!e)
    return e;

  switch (e->discr)
    {
    case SL_F_TRUE:
    case SL_F_FALSE:
      return e;
    case SL_F_NOT:
      {
	assert (e->size == 1);
	sl_exp_t *se = sl_exp_typecheck_exists (ctx, e->args[0]);
	if (se == NULL)
	  return NULL;
	e->args[0] = se;
	return e;
      }
    case SL_F_TOBOOL:
    case SL_F_AND:
      return sl_exp_typecheck_and (ctx, e);
    case SL_F_IMPLIES:
      {
	assert (e->size == 2);
	//done in mk_implies
	e->args[0] = sl_exp_typecheck_exists (ctx, e->args[0]);
	e->args[1] = sl_exp_typecheck_exists (ctx, e->args[1]);
	if (!e->args[0] || !e->args[1])
	  return NULL;
	return e;
      }
    case SL_F_EXISTS:
      {
	return sl_exp_typecheck_exists (ctx, e);
      }
    default:
      {
	sl_error (0, "sl_exp_typecheck", "syntax error in formula");
	return NULL;
      }
    }
}

/*
 * ======================================================================
 * Translation to formula
 * ======================================================================
 */

void
sl_exp_push_pure (sl_context_t * ctx, sl_exp_t * e, sl_pure_array * form)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  assert (NULL != e);
  assert (NULL != form);
  switch (e->discr)
    {
    case SL_F_EQ:
      {
	//the variables implied in the equality
	uint_t v1 = e->args[0]->p.sid;
	uint_t v2 = e->args[1]->p.sid;
	sl_pure_push (form, SL_PURE_EQ, v1, v2);
	break;
      }
    case SL_F_DISTINCT:
      {
	//the variables implied in the equality
	uint_t v1 = e->args[0]->p.sid;
	uint_t v2 = e->args[1]->p.sid;
	sl_pure_push (form, SL_PURE_NEQ, v1, v2);
	break;
      }
    default:
      break;			/* nothing to be done */
    }
}

/**
 * Translates the AST in e to a space formula.
 * @param f the AST of the points-to formula
 * @return the space formula or NULL of error
 */
sl_space_t *
sl_mk_form_junk (sl_exp_t * f)
{
  assert (f && f->discr == SL_F_JUNK);
  sl_space_t *sigma = (sl_space_t *) malloc (sizeof (sl_space_t));
  sigma->kind = SL_SPACE_JUNK;
  sigma->is_precise = (f != NULL) ? false : true;
  return sigma;
}

/**
 * Translates the AST in e to a points-to space formula.
 * @param env  formula containing the environment of variables used
 * @param f the AST of the points-to formula
 * @return the space formula or NULL of error
 */
sl_space_t *
sl_mk_form_pto (sl_context_t * ctx, sl_exp_t * f)
{
  assert (f && f->discr == SL_F_PTO && f->size == 2);
  sl_exp_t *v = f->args[0];
  sl_exp_t **fv = NULL;
  uint_t fv_size = 1;
  sl_space_t *sigma = (sl_space_t *) malloc (sizeof (sl_space_t));
  sigma->kind = SL_SPACE_PTO;
  sigma->is_precise = true;

  if (v->discr == SL_F_LVAR)
    sigma->m.pto.sid = v->p.sid;
  //is in context

  // fill the set of locations from fv which may be ref or sref
  if (f->args[1]->discr == SL_F_REF)
    {
      fv_size = 1;
      fv = &f->args[1];
    }
  else if (f->args[1]->discr == SL_F_SREF)
    {
      fv_size = f->args[1]->size;
      fv = f->args[1]->args;
    }
  else
    {
      sl_error (1, "Building points-to formula: bad type for location ",
		sl_var_name (ctx->lvar_env, v->p.sid, SL_TYP_RECORD));
      sl_space_free (sigma);
      return NULL;
    }
  sigma->m.pto.dest = sl_uid_array_new ();
  sl_uid_array_reserve (sigma->m.pto.dest, fv_size);
  sigma->m.pto.fields = sl_uid_array_new ();
  sl_uid_array_reserve (sigma->m.pto.fields, fv_size);
  uint_t i;
  for (i = 0; i < fv_size; i++)
    {
      assert (fv[i]->discr == SL_F_REF && fv[i]->size == 2);
      uint_t dest = UNDEFINED_ID;
      if (fv[i]->args[1]->discr == SL_F_LVAR)
	dest = fv[i]->args[1]->p.sid;
      else
	assert (0);
      assert (fv[i]->args[0]->discr == SL_F_FIELD);
      uint_t fld = fv[i]->args[0]->p.sid;
      // because the term has been built
      assert (fld != UNDEFINED_ID);
      // notice that we may have dest == UNDEFINED_ID == VNIL_ID
      sl_uid_array_push (sigma->m.pto.dest, dest);
      sl_uid_array_push (sigma->m.pto.fields, fld);
    }
  return sigma;
}

sl_space_t *
sl_mk_form_loop (sl_context_t * ctx, sl_exp_t * e)
{
  sl_space_t *ret = NULL;
  assert (e && e->discr == SL_F_LOOP);
  //there is only one argument
  if (e->size != 1)
    {
      sl_error (1, "Loop expression", "bad number of arguments");
      return ret;
    }
  //generate the argument which shall be a predicate call
  if (e->args[0]->discr != SL_F_PRED)
    {
      sl_error (1, "Loop expression", "bad predicate argument");
      return ret;
    }
  ret = sl_mk_form_pred (ctx, e->args[0]);
  if (ret != NULL)
    {
      /* if no error, set loop in the predicate call */
      ret->m.ls.is_loop = true;
    }
  return ret;
}

sl_space_t *
sl_mk_form_pred (sl_context_t * ctx, sl_exp_t * e)
{
  assert (e && e->discr == SL_F_PRED && e->size >= 1);
  //check that the type of actual arguments is correct
  sl_uid_array *actuals = sl_uid_array_new ();
  sl_uid_array_reserve (actuals, e->size);
  uint_t *actuals_ty = (uint_t *) malloc (e->size * sizeof (uint_t));

  const char *pname = sl_pred_name (e->p.sid);
  assert (NULL != pname);
  uint_t i;
  for (i = 0; i < e->size; i++)
    {
      if (e->args[i]->discr != SL_F_LVAR || e->args[i]->size != 0)
	{
	  sl_error (1, "Predicate call to ", pname);
	  sl_error (1, "Bad (last) parameters.", "");
	  free (actuals);
	  free (actuals_ty);
	  return NULL;
	}
      uint_t pi = e->args[i]->p.sid;
      sl_uid_array_push (actuals, pi);
      actuals_ty[i] = sl_var_record (ctx->lvar_env, pi);
    }
  uint_t pid = sl_pred_typecheck_call (e->p.sid, actuals_ty, e->size);
  free (actuals_ty);

  //generate the corresponding space formula
  sl_space_t *pcall = (sl_space_t *) malloc (sizeof (sl_space_t));
  pcall->kind = SL_SPACE_LS;
  pcall->is_precise = true;
  pcall->m.ls.pid = pid;
  pcall->m.ls.args = actuals;
  pcall->m.ls.is_loop = false;

  return pcall;
}

sl_space_t *
sl_mk_form_sep (sl_context_t * ctx, sl_exp_t * e)
{
  sl_space_t *ret = NULL;
  assert (e && (e->discr == SL_F_SSEP));

  //allocate the space formula
  ret = (sl_space_t *) malloc (sizeof (sl_space_t));
  ret->kind = SL_SPACE_SSEP;
  ret->is_precise = true;
  ret->m.sep = sl_space_array_new ();
  //reserve at least the number of arguments here
  sl_space_array_reserve (ret->m.sep, e->size);
  for (uint_t i = 0; i < e->size; i++)
    {
      sl_space_t *ei = sl_exp_push_space (ctx, e->args[i]);
      if (ei == NULL)
	continue;
      //is_precise attribute is propagated to parents
      if (ei->is_precise == false)
	ret->is_precise = false;
      if (ei->kind == ret->kind)
	{
	  //same separation operator, remove the intermediary node
	  for (uint_t j = 0; j < sl_vector_size (ei->m.sep); j++)
	    {
	      sl_space_t *eij = sl_vector_at (ei->m.sep, j);
	      sl_space_array_push (ret->m.sep, eij);
	      sl_vector_at (ei->m.sep, j) = NULL;
	    }
	  sl_space_array_delete (ei->m.sep);
	  free (ei);
	}
      else
	{
	  //different operator, push the formula as arguments
	  sl_space_array_push (ret->m.sep, ei);
	}
    }
  return ret;
}

sl_space_t *
sl_exp_push_space (sl_context_t * ctx, sl_exp_t * e)
{
  assert (e);

  sl_space_t *ret = NULL;
  switch (e->discr)
    {
    case SL_F_EMP:
      /* nothing */
      break;
    case SL_F_JUNK:
      {
	ret = sl_mk_form_junk (e);
	break;
      }
    case SL_F_PTO:
      {
	ret = sl_mk_form_pto (ctx, e);
	break;
      }
    case SL_F_PRED:
      {
	ret = sl_mk_form_pred (ctx, e);
	break;
      }
    case SL_F_SSEP:
      {
	ret = sl_mk_form_sep (ctx, e);
	break;
      }
    default:
      sl_error (1, "sl_exp_push_space", "not a space formula");
      break;
    }
  return ret;
}


void
sl_exp_push_top (sl_context_t * ctx, sl_exp_t * e, sl_form_t * form)
{
  assert (ctx != NULL);
  assert (e != NULL);
  assert (form != NULL);

  //copy variables from context to formula
  if (form->lvars != NULL && form->lvars != ctx->lvar_env)
    sl_var_array_delete (form->lvars);
  form->lvars = ctx->lvar_env;
#ifndef NDEBUG
  fprintf (stdout, "\nsl_exp_push_top:\n\t");
  sl_var_array_fprint (stdout, form->lvars, "lvars");
  fprintf (stdout, "\n\t");
#endif
  //fill other parts of the formula
  switch (e->discr)
    {
      /* boolean operations */
    case SL_F_FALSE:
    case SL_F_TRUE:
      return;			/* nothing to be done */
    case SL_F_AND:
      {
	for (uint_t i = 0; i < e->size; i++)
	  sl_exp_push_top (ctx, e->args[i], form);
	break;
      }
    case SL_F_EXISTS:
      {
	//existential variables are already in form->? vars
	for (uint_t i = 0; i < e->size; i++)
	  sl_exp_push_top (ctx, e->args[i], form);
	break;
      }
    case SL_F_NOT:
    case SL_F_OR:
    case SL_F_IMPLIES:
    case SL_F_FORALL:
      {
	//this is an error, no translation is possible
	sl_error (0, "sl_exp_push_top", "boolean operation not allowed");
	return;
      }

      /* pure constraints */
    case SL_F_EQ:
    case SL_F_DISTINCT:
      {
#ifndef NDEBUG
	fprintf (stdout, "Push pure:");
	sl_exp_printf (stdout, ctx, e);
	fflush (stdout);
#endif
	sl_exp_push_pure (ctx, e, form->pure);
	break;
      }
      /*
       * towards space
       * operations
       */
    case SL_F_TOBOOL:
      {
	form->space = sl_exp_push_space (ctx, e->args[0]);
	break;
      }
    default:
      {
	//this is an error, no translation is possible
	sl_error (0, "sl_exp_push_top", "space operation not allowed");
	return;
      }
    }
}

/** Translation form AST to SL formula and push into the global formulas.
 */
void
sl_exp_push (sl_context_t * ctx, sl_exp_t * e, int ispos)
{
#ifndef NDEBUG
  //printing now:
  fprintf (stdout, "Push %stive formula:\n", (ispos) ? "posi" : "nega");
  sl_exp_printf (stdout, ctx, e);
  fprintf (stdout, "\nwith context: ");
  sl_var_array_fprint (stdout, ctx->lvar_env, "lvars");
  fflush (stdout);
#endif
  if (!e)
    return;

  sl_form_t *form =
    (ispos == 0) ? sl_prob_get_nform_last () : sl_prob_get_pform ();

  sl_exp_push_top (ctx, e, form);

  return;
}
