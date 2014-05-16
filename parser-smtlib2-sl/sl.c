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

#include "noll.h"
#include "noll_ta_symbols.h"

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

int noll_error_parsing = 0;

/*
 * ======================================================================
 * Messages
 * ======================================================================
 */

void
noll_error (int level, const char *fun, const char *msg)
{
  fprintf (stderr, "Error of level %d in %s: %s.\n", level, fun, msg);
  if (level == 0)
    //terminate
    exit (0);
  else
    noll_error_parsing = level;
}

void
noll_error_args (int level, const char *fun, uint_t size, const char *expect)
{
  fprintf (stderr,
	   "Error of level %d in %s: bad number (%d) of arguments, expected (%s).\n",
	   level, fun, size, expect);
  if (level == 0)
    //terminate
    exit (0);
  else
    noll_error_parsing = level;
}

void
noll_error_id (int level, char *fun, const char *name)
{
  fprintf (stderr,
	   "Error of level %d in %s: identifier '%s' is not declared.\n",
	   level, fun, name);
  if (level == 0)
    //terminate
    exit (0);
  else
    noll_error_parsing = level;
}

/*
 * ======================================================================
 * Globals
 * ======================================================================
 */

void
noll_init ()
{
  noll_record_init ();
  noll_field_init ();
  //TODO:remove noll_vars_init();
  noll_pred_init ();
  noll_entl_init ();
}

/*
 * ======================================================================
 * Context
 * ======================================================================
 */

noll_context_t *
noll_mk_context (void)
{
  noll_context_t *r =
    (noll_context_t *) malloc (sizeof (struct noll_context_t));

  /* initialize the global tables for the analysis */
  noll_init ();

#ifndef NDEBUG
  printf ("noll_mk_context reset qstack\n");
#endif
  /* initialize the stack of location variables to store
   * one global variable (nil) */
  r->lvar_stack = noll_uint_array_new ();
  noll_uint_array_push (r->lvar_stack, 1);

  /* initialize the set of location variables to store
   * nil */
  r->lvar_env = noll_var_array_new ();
  noll_var_register (r->lvar_env, "nil",
		     noll_record_find ("void"), NOLL_SCOPE_GLOBAL);


  /* initialize the stack of sloc vars to the empy stack */
  r->svar_stack = noll_uint_array_new ();
  noll_uint_array_push (r->svar_stack, 0);

  /* initialize the set of sloc vars to be empty */
  r->svar_env = noll_var_array_new ();

  /* the current procedure name */
  r->pname = NULL;

  return r;
}

/**
 * Destroy context data at the end of parsing.
 */
void
noll_del_context (noll_context_t * ctx)
{
  //ctx->l_env is in general in use
  noll_uint_array_delete (ctx->lvar_stack);
  noll_var_array_delete (ctx->lvar_env);
  noll_uint_array_delete (ctx->svar_stack);
  noll_var_array_delete (ctx->svar_env);
  free (ctx->pname);
  //not in use, usually
  free (ctx);
}

/**
 * Unlink context variables at the end of define-fun.
 * It is called before noll_pop_quant
 */
void
noll_pop_context (noll_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "noll_pop_context start\n");
  fflush (stdout);
#endif
  /*
   * the entries for exists and parameters will be deleted after that
   * by noll_pop_quant no global variables added
   */
  assert (noll_vector_at (ctx->lvar_stack, 0) == 1);
  assert (noll_vector_at (ctx->svar_stack, 0) == 0);
  /* the location array is reused in the function, 
   * thus only forget it and reenter "nil"
   */
  ctx->lvar_env = noll_var_array_new ();
  noll_var_register (ctx->lvar_env, "nil",
		     noll_record_find ("void"), NOLL_SCOPE_GLOBAL);
  /* unset the predicate name is allocated */
  ctx->pname = NULL;
}

/**
 * Reinitialize the context to globals.
 * A new array shall be created for the @p ctx->*vars.
 */
void
noll_contex_restore_global (noll_context_t * ctx)
{
  assert (ctx != NULL);
  assert (ctx->lvar_env != NULL);
  assert (ctx->lvar_stack != NULL);
  assert (ctx->svar_env != NULL);
  assert (ctx->svar_stack != NULL);

#ifndef NDEBUG
  fprintf (stderr, "noll_context_restore_global: (begin) %d vars, %d svars\n",
	   noll_vector_at (ctx->lvar_stack, 0),
	   noll_vector_at (ctx->svar_stack, 0));
#endif
  // ctx->* vars have been copied in  the formulae
  // refill the context with the global variables
  noll_var_array *arr = ctx->lvar_env;
  //this array is in the formulae
  uint_t size = noll_vector_at (ctx->lvar_stack, 0);
  ctx->lvar_env = noll_var_array_new ();
  if (size > 0)
    noll_var_array_reserve (ctx->lvar_env, size);
  for (uint_t i = 0; i < size; i++)
    noll_var_array_push (ctx->lvar_env,
			 noll_var_copy (noll_vector_at (arr, i)));
  arr = ctx->svar_env;
  //this array is in the formulae
  size = noll_vector_at (ctx->svar_stack, 0);
  ctx->svar_env = noll_var_array_new ();
  if (size > 0)
    noll_var_array_reserve (ctx->svar_env, size);
  for (uint_t i = 0; i < size; i++)
    noll_var_array_push (ctx->svar_env,
			 noll_var_copy (noll_vector_at (arr, i)));

#ifndef NDEBUG
  fprintf (stderr, "noll_context_restore_global: (end) %d vars, %d svars\n",
	   noll_vector_size (ctx->lvar_env),
	   noll_vector_size (ctx->svar_env));
#endif
  return;
}

void
noll_context_fprint (FILE * f, noll_context_t * ctx)
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
      for (uint_t i = 0; i < noll_vector_size (ctx->lvar_stack); i++)
	fprintf (stdout, "%d,", noll_vector_at (ctx->lvar_stack, i));
    }
  fprintf (stdout, "\n\t]\n");

  fprintf (f, "\tlvar_env => ");
  if (ctx->lvar_env == NULL)
    fprintf (f, "NULL");
  else
    fprintf (f, "%d", noll_vector_size (ctx->lvar_env));

  fprintf (stdout, "\n\tsvar_stack=[");
  if (ctx->lvar_stack == NULL)
    fprintf (f, "NULL");
  else
    {
      for (uint_t i = 0; i < noll_vector_size (ctx->svar_stack); i++)
	fprintf (stdout, "%d,", noll_vector_at (ctx->svar_stack, i));
    }
  fprintf (stdout, "\n\t]\n");

  fprintf (f, "\tsvar_env => ");
  if (ctx->svar_env == NULL)
    fprintf (f, "NULL");
  else
    fprintf (f, "%d", noll_vector_size (ctx->svar_env));

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
noll_set_logic (noll_context_t * ctx, const char *logic)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (!strcmp (logic, "QF_NOLL"))
    {
      noll_error (0, "set-logic", "unknown logic");
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
noll_type_t *
noll_mk_fun_decl (noll_context_t * ctx, const char *name, noll_type_t * rty)
{
  switch (rty->kind)
    {
    case NOLL_TYP_RECORD:
      {
	/* global variable declaration
	 * register it in the array of variables
	 */
	noll_var_register (ctx->lvar_env, name, rty, NOLL_SCOPE_GLOBAL);
	if (rty != NULL)
	  noll_vector_at (ctx->lvar_stack, 0) += 1;
	return rty;
      }
    case NOLL_TYP_SETLOC:
      {
	//variable declaration
	// register it in the array of variables
	noll_var_register (ctx->svar_env, name, rty, NOLL_SCOPE_GLOBAL);
	if (rty != NULL)
	  noll_vector_at (ctx->svar_stack, 0) += 1;
	return rty;
      }
    case NOLL_TYP_FIELD:
      {
	//field declaration
	// register it in the array of fields
	noll_field_register (name, rty);
	return rty;
      }
    default:
      //error, return NULL below
      break;
    }
  return NULL;
}

uint_t
noll_exp_typecheck_pred_basic_case (const char *name,
				    uint_t nrec_p, noll_exp_t * fequals)
{

  /* TODO: check correctly the two way predicates */
  if ((fequals == NULL)		/* empty basic case */
      || (fequals->discr != NOLL_F_EQ && nrec_p < 4)	/* one way predicate */
      || (fequals->discr != NOLL_F_AND && nrec_p >= 4)	/* two way predicate */
    )
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Base case not well defined ", "(number of equalities)");
      return UNDEFINED_ID;
    }
  if (fequals->discr == NOLL_F_EQ)
    {
      /* the two variables are the first parameters */
      uint_t v1 = UNDEFINED_ID;
      uint_t v2 = UNDEFINED_ID;
      if (fequals->args[0]->discr == NOLL_F_LVAR)
	v1 = fequals->args[0]->p.sid;
      if (fequals->args[1]->discr == NOLL_F_LVAR)
	v2 = fequals->args[1]->p.sid;
      if ((v1 != 1 || v2 != 2) && (v1 != 2 || v2 != 1))
	{
	  noll_error (1, "Building predicate definition ", name);
	  noll_error (1, "Base case not well defined ",
		      "(equalities on bad parameters)");
	  return UNDEFINED_ID;
	}
      /* else, the predicate may be built */
    }
  else
    {
      /* TODO: see how to check that it is a two way predicate
       * Now, only two equalities between variables 1 = 3 and 2 = 4,
       * thus the node shall be an 'and' and
       *      the inner nodes shall be equalities
       */
      if ((fequals->discr != NOLL_F_AND) ||
	  (fequals->size != 2) ||
	  (fequals->args[0]->discr != NOLL_F_EQ) ||
	  (fequals->args[0]->discr != NOLL_F_EQ))
	{
	  noll_error (1, "Building predicate definition ", name);
	  noll_error (1, "Base case not well defined ",
		      "(and with two equalities)");
	  return UNDEFINED_ID;
	}
      /*
       * TODO: check the equalities
       */
      /* else, the predicate may be built */
    }

  return 0;
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
noll_mk_fun_def (noll_context_t * ctx, const char *name, uint_t npar,
		 noll_type_t * rety, noll_exp_t * def)
{
  /* assert:name is unique */
  if (strcmp (ctx->pname, name))
    {
      /* name does not correspond to this predicate definition */
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect predicate name in ", name);
      return UNDEFINED_ID;
    }
  /*
   * assert: no global variables except the "nil" constant
   * may be defined before the predicate definition,
   * since no global context is kept for the definition of
   * the predicate
   */
  if (noll_vector_at (ctx->lvar_stack, 0) >= 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Global variables declared before ", name);
      return UNDEFINED_ID;
    }
  /*
   * assert: number of parameters is at least 2 and
   * exactly the ctx->lvar_stack[1]
   */
  if (noll_vector_size (ctx->lvar_env) <= 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Empty set of parameters in ", name);
      return UNDEFINED_ID;
    }
  if (noll_vector_at (ctx->lvar_stack, 1) < 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect number of parameters (< 2) in ", name);
      return UNDEFINED_ID;
    }
  if ((noll_vector_at (ctx->lvar_stack, 1) > noll_vector_size (ctx->lvar_env))
      || (noll_vector_at (ctx->lvar_stack, 1) != npar))
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect number of parameters in ", name);
      return UNDEFINED_ID;
    }
  /* assert:rety sort shall be Space */
  if ((rety == NULL) || (rety->kind != NOLL_TYP_SPACE))
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect result type (!= Space) ", name);
      return UNDEFINED_ID;
    }
  /*
   * Check the syntax of predicates while
   * the predicate definition is built
   */
  /* cond 0: all the parameters are of record type */
  for (uint_t i = 1; i <= npar; i++)
    {
      if (noll_var_record (ctx->lvar_env, i) == UNDEFINED_ID)
	{
	  noll_error (1, "Building predicate definition ", name);
	  noll_error (1, "Parameter not of record type ", name);
	  return UNDEFINED_ID;
	}
    }
  /*
   * cond 1: The first two parameters are of the same sort, the
   * sort of the predicate.
   *
   * TODO: for dll, the first four parameters shall have the same sort.
   * TODO: the sort of the remaining parameters shall be checked also!
   */
  /* first parameters is at position 1 in lvar_env */
  uint_t pred_ty = noll_var_record (ctx->lvar_env, 1);
  uint_t nrec_p = 0;
  while ((nrec_p < npar)
	 && (noll_var_record (ctx->lvar_env, nrec_p + 1) == pred_ty))
    nrec_p++;
#ifndef NDEBUG
  fprintf (stderr, "noll_mk_fun_def: Number of recursive parameters %d.\n",
	   nrec_p);
#endif
  if (nrec_p < 2)
    {
      char str[10];
      snprintf (str, 10, "%d", nrec_p);
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect number of recursive parameters (< 2), i.e., ",
		  str);
      return UNDEFINED_ID;
    }
  /* nrec_p is the first parameter of type different from pred_ty */
  /* TODO: check the other parameters */
  /*
     for (uint_t i = nrec_p; i < npar; i++) {
     if (noll_var_record(ctx->lvar_env, i) == pred_ty) {
     char str[10];
     snprintf(str, 10, "%d", i);
     noll_error(1, "Building predicate definition ", name);
     noll_error(1, "Incorrect type of parameter ", str);
     return UNDEFINED_ID;
     }
     }
   */

  /* cond 2: the def has the form(tospace(exists etc))) */
  if (def->discr != NOLL_F_TOSPACE || def->size != 1)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "First operator is not 'tospace' ", "");
      return UNDEFINED_ID;
    }
  if (def->args == NULL || def->args[0]->discr != NOLL_F_OR)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Second operator is not 'or' ", "");
      return UNDEFINED_ID;
    }
  noll_exp_t *fequals = def->args[0]->args[0];
  noll_exp_t *fexists = def->args[0]->args[1];

  /*
   * cond 3: check the basic case
   */
  if (noll_exp_typecheck_pred_basic_case (name, nrec_p, fequals)
      == UNDEFINED_ID)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Bad type for predicate ", "");
      return UNDEFINED_ID;
    }

  /*
   * cond 4: < exists > defines variables such that
   *
   *      -only one variable of the recursive type pred_ty
   *
   *      -the other variables are of type typinf the fields of pred_ty
   */
  /*
   * Notice: qarr == ctx->l_env and npar == fexists->p.quant.start
   */
  noll_var_array *qarr = fexists->p.quant.lvars;
  /* check the starting index of existentially quantified vars */
  if ((qarr == NULL) || ((npar + 1) != fexists->p.quant.lstart))
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Exists without variables ", "(or internal error)");
      return UNDEFINED_ID;
    }
  uint_t uid = 0;		/* the identifier of the first recursive variable */
  for (uint_t i = fexists->p.quant.lstart; i < noll_vector_size (qarr); i++)
    {
      noll_var_t *vi = noll_vector_at (qarr, i);
      if (vi)
	{
	  uint_t vi_ty = noll_var_record (qarr, i);
	  /* the type of variables shall be record */
	  if (vi_ty == UNDEFINED_ID)
	    {
	      noll_error (1, "Building predicate definition ", name);
	      noll_error (1, "Exists quantifies a non-location variable ",
			  "");
	      return UNDEFINED_ID;
	    }
	  if (uid == 0)
	    uid = i;
	}
    }
  /* a variable with the same type as the predicate shall exists */
  if (uid == 0)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Exists does not quantify a variable ",
		  "inside the list segment");
      return UNDEFINED_ID;
    }
  /*
   * cond 5: the formula in exists starts by (tobool(ssep(pto...) (...)
   * (recursive call))
   */
  noll_exp_t *qform = fexists->args[0];
  if (qform->discr != NOLL_F_TOBOOL || qform->size != 1 || qform->args == NULL
      || qform->args[0]->discr != NOLL_F_SSEP || qform->args[0]->size < 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Formula inside exists ", "is not (tobool (ssep ...))");
      return UNDEFINED_ID;
    }
  /*
   * goes through the arguments of ssep and builds two spatial formulas
   * - one for pto - one for nesting
   */
  noll_exp_t *sepform = qform->args[0];
  if (sepform->size < 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Formula inside exists ",
		  "shall have at least two subformulas");
      return UNDEFINED_ID;
    }
  noll_space_t *sigma_0 = NULL;
  noll_space_t *sigma_1 = NULL;
  /*
   * Notice: the size of sigma_1 is the size of sepform - 2 (sigma_0
   * and the recursive call are removed)
   */
  /*
   * TODO: store the recursive call for dll and skiplists
   */
  if (sepform->size > 2)
    {
      sigma_1 = (noll_space_t *) malloc (sizeof (noll_space_t));
      sigma_1->kind = NOLL_SPACE_SSEP;
      sigma_1->m.sep = noll_space_array_new ();
      noll_space_array_reserve (sigma_1->m.sep, (sepform->size - 2));
    }
  uint_t rec_call = 0;
  for (uint_t i = 0; i < sepform->size; i++)
    {
      noll_exp_t *si = sepform->args[i];
      switch (si->discr)
	{
	case NOLL_F_PTO:
	  {
	    /*
	     * may be pto from in or from a variable !=
	     * in and u
	     */
	    noll_space_t *pto = noll_mk_form_pto (ctx, si);
	    //add to sigma_0 or sigma_1
	    if (pto->m.pto.sid == VID_FST_PARAM)
	      {
		// VID_FST_PARAM is the index of the "in" parameter
		if (sigma_0 != NULL)
		  {
		    noll_error (1, "Building predicate definition ", name);
		    noll_error (1, "Points-to link",
				"(more than one from in parameter)");
		    noll_space_free (sigma_0);
		    noll_space_free (sigma_1);
		    return UNDEFINED_ID;
		  }
		sigma_0 = pto;
	      }
	    else
	      {
		if (NULL == sigma_1)
		  {
		    noll_error (1, "Building predicate definition ", name);
		    noll_error (1,
				"One points-to not from the first parameter ",
				"(the input)");
		    noll_space_free (sigma_0);
		    noll_space_free (sigma_1);
		    return UNDEFINED_ID;
		  }
		noll_space_array_push (sigma_1->m.sep, pto);
	      }
	    break;
	  }
	case NOLL_F_LOOP:
	  {
	    /* before the non-recursive call of a predicate */
	    if (si->size != 1 || si->args[0]->discr != NOLL_F_PRED)
	      {
		noll_error (1, "Building predicate definition ", name);
		noll_error (1, "Incorrect loop space formula ",
			    "(argument not a predicate call)");
		noll_space_free (sigma_0);
		noll_space_free (sigma_1);
		return UNDEFINED_ID;
	      }
	    else
	      {
		noll_exp_t *fpred = si->args[0];
		/* shall not be a recursive call */
		if (fpred->p.sid == UNDEFINED_ID)
		  {
		    noll_error (1, "Building predicate definition ", name);
		    noll_error (1, "Incorrect loop space formula ",
				"(argument a recursive predicate call)");
		    noll_space_free (sigma_0);
		    noll_space_free (sigma_1);
		    return UNDEFINED_ID;
		  }
		else
		  {
		    noll_space_t *loop = noll_mk_form_loop (ctx, si);
		    assert (NULL != sigma_1);
		    noll_space_array_push (sigma_1->m.sep, loop);
		  }
	      }
	    break;
	  }
	case NOLL_F_PRED:
	  {
	    /* check the predicate call */
	    if (si->p.sid == UNDEFINED_ID)
	      {
		/* it is a recursive call */
		if (rec_call >= 1)
		  {
		    noll_error (1, "Building predicate definition ", name);
		    noll_error (1, "Recursive call ",
				"(more than one recursive call)");
		    noll_space_free (sigma_0);
		    noll_space_free (sigma_1);
		    return UNDEFINED_ID;
		  }
		rec_call++;
		/*
		 * check that parameters are the same
		 * except the first one(nrec_p == 2)
		 * or two(nrec_p == 4)
		 */
		if (nrec_p == 2)
		  {
		    if ((si->size < 2) || (si->size != npar)
			|| (si->size
			    != noll_vector_at (ctx->lvar_stack, 1))
			|| (si->args == NULL) || (si->args[0] == NULL)
			|| (si->args[0]->discr != NOLL_F_LVAR))
		      {
			noll_error (1, "Building predicate definition ",
				    name);
			noll_error (1, "Recursive call ",
				    "(bad number of arguments)");
			noll_space_free (sigma_0);
			noll_space_free (sigma_1);
			return UNDEFINED_ID;
		      }
		    uint_t p0 = si->args[0]->p.sid;
		    if ((p0 == UNDEFINED_ID)
			|| (noll_var_record (ctx->lvar_env, p0) != pred_ty))
		      {
			noll_error (1, "Building predicate definition ",
				    name);
			noll_error (1, "Recursive call ",
				    "(bad first parameter)");
			noll_space_free (sigma_0);
			noll_space_free (sigma_1);
			return UNDEFINED_ID;
		      }
		    /*
		     * else, this parameter is
		     * ok, check for equality the
		     * remainder parameters
		     */
		  }
		else
		  //nrec_p == 4
		  {
		    if (si->size < 2 || si->size != nrec_p
			|| si->args == NULL || si->args[0] == NULL
			|| si->args[1] == NULL
			|| si->args[0]->discr != NOLL_F_LVAR
			|| si->args[1]->discr != NOLL_F_LVAR)
		      {
			noll_error (1, "Building predicate definition ",
				    name);
			noll_error (1, "Recursive call ",
				    "(bad number of parameters)");
			noll_space_free (sigma_0);
			noll_space_free (sigma_1);
			return UNDEFINED_ID;
		      }
		    uint_t p0 = si->args[0]->p.sid;
		    uint_t p1 = si->args[1]->p.sid;
		    if (p0 == UNDEFINED_ID || p1 == UNDEFINED_ID
			|| noll_var_record (ctx->lvar_env, p0) != pred_ty
			|| noll_var_record (ctx->lvar_env, p1) != pred_ty
			|| p1 != 2)
		      {
			noll_error (1, "Building predicate definition ",
				    name);
			noll_error (1, "Recursive call ",
				    "(bad first two parameters)");
			noll_space_free (sigma_0);
			noll_space_free (sigma_1);
			return UNDEFINED_ID;
		      }
		    /*
		     * else, these parameters are
		     * ok, check for equality the
		     * remainder parameters
		     */
		  }
		/*
		 * check that the remainder of
		 * parameters are equal to the formal
		 * ones except for dll
		 */
		uint_t i = (nrec_p == 2) ? 1 : 3;
		for (; i < npar; i++)
		  {
		    if (si->args[i]->discr != NOLL_F_LVAR
			|| ((noll_vector_at (ctx->lvar_env, i + 1))->vid
			    != si->args[i]->p.sid))
		      {
			noll_error (1, "Building predicate definition ",
				    name);
			noll_error (1, "Recursive call ",
				    "(not equal non-recursive parameters)");
			noll_space_free (sigma_0);
			noll_space_free (sigma_1);
			return UNDEFINED_ID;
		      }
		  }
	      }
	    else
	      {
		/* non recursive predicate call */
		noll_space_t *pcall = noll_mk_form_pred (ctx, si);
		//put this call into sigma_1
		noll_space_array_push (sigma_1->m.sep, pcall);
	      }
	    break;
	  }
	default:
	  break;
	}			//end switch
    }				/* end for */
  /* last: checks sigma_0 is not null */
  if (sigma_0 == NULL)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "No points-to part ", "");
      // noll_space_free(sigma_0);
      noll_space_free (sigma_1);
      return UNDEFINED_ID;
    }
  /*
   * build the record for this predicate definition and register it
   */
  noll_pred_binding_t *pdef =
    (noll_pred_binding_t *) malloc (sizeof (noll_pred_binding_t));
  pdef->pargs = (nrec_p == 2) ? 0 : 1;
  pdef->fargs = npar;
  pdef->vars = ctx->lvar_env;
  pdef->sigma_0 = sigma_0;
  pdef->sigma_1 = sigma_1;

  /* restore the global environment */
  noll_contex_restore_global (ctx);

  /* register the  predicate */
  return noll_pred_register (name, pdef);
}

int
noll_assert (noll_context_t * ctx, noll_exp_t * term)
{
  //check that the formula is not null
  if (!term)
    {
      noll_error (1, "noll_assert", "null formula");
      return 0;
    }
  /* if the local environment is not empty, signal it */
  if ((noll_vector_size (ctx->lvar_stack) > 1)
      || (noll_vector_size (ctx->svar_stack) > 1))
    {
      noll_error (1, "noll_assert", "non empty local environment");
      return 0;
    }
  /* typecheck the formula and do simplifications, if needed */
  noll_exp_t *form = noll_exp_typecheck (ctx, term);
  if (form == NULL)
    {
      noll_error (1, "noll_assert", "typechecking error");
      return 0;
    }
  /* translate into a formula and
   * fill the positive or negative formulae depending on the first operator
   */
  if (form->discr == NOLL_F_NOT)
    noll_exp_push (ctx, form->args[0], 0);
  /* push in negative */
  else
    noll_exp_push (ctx, form, 1);
  /* push in positive */

  /* restore the global environment */
  noll_contex_restore_global (ctx);

  return 1;
}

/**
 * Sets the command.
 */
int
noll_check (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);		// to avoid "unused parameter" warning
    }
  if (noll_error_parsing > 0)
    {
      assert (noll_prob->smt_fname != NULL);
      noll_error (0, "noll_check", "stop check because of parsing error");
      return 0;
    }

  noll_entl_set_cmd (NOLL_FORM_SAT);
  return noll_entl_solve ();
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
noll_push_var (noll_context_t * ctx, const char *name, noll_type_t * vty)
{
  if (!ctx)
    return;

  uid_t vid = UNDEFINED_ID;
  if (vty->kind == NOLL_TYP_RECORD)
    {
      assert (ctx->lvar_env != NULL);
      noll_var_t *v = noll_var_new (name, vty, NOLL_SCOPE_LOCAL);
      noll_var_array_push (ctx->lvar_env, v);
      v->vid = noll_vector_size (ctx->lvar_env) - 1;
      //update the number of elements in the top of the stack
      uint_t top_stack = noll_vector_size (ctx->lvar_stack) - 1;
      noll_vector_at (ctx->lvar_stack, top_stack) += 1;
    }
  else if (vty->kind == NOLL_TYP_SETLOC)
    {
      assert (ctx->svar_env != NULL);
      noll_var_t *v = noll_var_new (name, vty, NOLL_SCOPE_LOCAL);
      noll_var_array_push (ctx->svar_env, v);
      v->vid = noll_vector_size (ctx->svar_env) - 1;
      //update the number of elements in the top of the stack
      uint_t top_stack = noll_vector_size (ctx->svar_stack) - 1;
      noll_vector_at (ctx->svar_stack, top_stack) += 1;
    }
  else
    assert (0);
}

int
noll_push_quant (noll_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "push_quant start: ");
  noll_context_fprint (stdout, ctx);
#endif
  //the NOLL supports only 2 levels of nesting and only inside define - fun
  if (noll_vector_size (ctx->lvar_stack) >= 3)
    {
      noll_error (0, "noll_push_quant", "too much nesting");
      return 0;
    }
  noll_uint_array_push (ctx->lvar_stack, 0);
  noll_uint_array_push (ctx->svar_stack, 0);
  return 1;
}

int
noll_pop_quant (noll_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "pop_quant start: ");
  noll_context_fprint (stdout, ctx);
#endif
  if (noll_vector_size (ctx->lvar_stack) <= 1)
    {
      noll_error (0, "noll_pop_quant", "too much pops");
      return 0;
    }
  noll_uint_array_pop (ctx->lvar_stack);
  noll_uint_array_pop (ctx->svar_stack);
  return 1;
}

noll_exp_t *
noll_mk_op (noll_expkind_t f, noll_exp_t ** args, uint_t size)
{
  uint_t i;
  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = f;
  res->size = size;
  res->args = NULL;
  if (size)
    {
      res->args = (noll_exp_t **) malloc (size * sizeof (noll_exp_t *));
      for (i = 0; i < size; i++)
	res->args[i] = args[i];
    }
  return res;
}

/**
 * This function is called
 * - either for predicate definition
 * - either at the top-most of a NOLL formula
 */
noll_exp_t *
noll_mk_exists (noll_context_t * ctx, noll_exp_t * term)
{
  //the exist variables are at the end of the stack,
  //i.e., top of ctx->* var_stack element,
  //in ctx->* _env

  uint_t nb_exists_lvar = noll_vector_last (ctx->lvar_stack);
  uint_t nb_exists_svar = noll_vector_last (ctx->svar_stack);

#ifndef NDEBUG
  fprintf (stdout, "mk_exists start lvar_stack=[");
  for (uint_t i = 0; i < noll_vector_size (ctx->lvar_stack); i++)
    fprintf (stdout, "%d,", noll_vector_at (ctx->lvar_stack, i));
  fprintf (stdout, "]\n");
  fprintf (stdout, "mk_exists exists lvar=[");
  for (uint_t i = nb_exists_lvar; i > 0; i--)
    {
      noll_var_t *vi = noll_vector_at (ctx->lvar_env,
				       noll_vector_size (ctx->lvar_env) - i);
      fprintf (stdout, "%s,", vi->vname);
    }
  fprintf (stdout, "]\n");

  fprintf (stdout, "mk_exists start svar_stack=[");
  for (uint_t i = 0; i < noll_vector_size (ctx->svar_stack); i++)
    fprintf (stdout, "%d,", noll_vector_at (ctx->svar_stack, i));
  fprintf (stdout, "]\n");
  fprintf (stdout, "mk_exists exists svar=[");
  for (uint_t i = nb_exists_svar; i > 0; i--)
    {
      noll_var_t *vi = noll_vector_at (ctx->svar_env,
				       noll_vector_size (ctx->svar_env) - i);
      fprintf (stdout, "%s,", vi->vname);
    }
  fprintf (stdout, "]\n");
#endif
  noll_exp_t *res = noll_mk_op (NOLL_F_EXISTS, &term, 1);
  res->p.quant.lvars = ctx->lvar_env;
  res->p.quant.lstart = noll_vector_size (ctx->lvar_env) - nb_exists_lvar;
  res->p.quant.lend = noll_vector_size (ctx->lvar_env);
  res->p.quant.svars = ctx->svar_env;
  res->p.quant.sstart = noll_vector_size (ctx->svar_env) - nb_exists_svar;
  res->p.quant.send = noll_vector_size (ctx->svar_env);
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
noll_exp_t *
noll_mk_app (noll_context_t * ctx, const char *name, noll_exp_t ** args,
	     uint_t size)
{
  if (size == 0)
    {
      //is null - ary symbols(true, false, emp, junk) or variable
      if (strcmp (name, "true") == 0)
	return noll_mk_true (ctx);
      if (strcmp (name, "false") == 0)
	return noll_mk_false (ctx);
      if (strcmp (name, "emp") == 0)
	return noll_mk_emp (ctx);
      if (strcmp (name, "junk") == 0)
	return noll_mk_junk (ctx);
      return noll_mk_symbol (ctx, name);
    }
  //is a predicate call(name args)
  return noll_mk_pred (ctx, name, args, size);
}

/** Build a term from this variable or field.
 */
noll_exp_t *
noll_mk_symbol (noll_context_t * ctx, const char *name)
{
  assert (ctx && name);
  noll_exp_t *ret = NULL;
  uint_t sid = UNDEFINED_ID;
  noll_type_t *typ = NULL;
#ifndef NDEBUG
  fprintf (stdout, "mk_symbol: start %s\n", name);
  fflush (stdout);
#endif
  /* special case of 'nil'?
     if (strcmp (name, "nil") == 0)
     {
     ret = noll_mk_op (NOLL_F_LVAR, NULL, 0);
     ret->p.sid = VNIL_ID;
     return ret;
     }
   */
  //search the variable environment
  // -search in the location env
  assert (ctx->lvar_env != NULL);
  sid = noll_var_array_find_local (ctx->lvar_env, name);
  if (sid != UNDEFINED_ID)
    typ = (noll_vector_at (ctx->lvar_env, sid))->vty;
  else
    {
      //search in the sloc env
      assert (ctx->svar_env != NULL);
      sid = noll_var_array_find_local (ctx->svar_env, name);

      if (sid != UNDEFINED_ID)
	typ = (noll_vector_at (ctx->svar_env, sid))->vty;
    }
  if (typ != NULL)
    {
      if (typ->kind == NOLL_TYP_RECORD)
	{
	  ret = noll_mk_op (NOLL_F_LVAR, NULL, 0);
	  ret->p.sid = sid;
	}
      else
	{
	  ret = noll_mk_op (NOLL_F_SVAR, NULL, 0);
	  ret->p.sid = sid;
	}
#ifndef NDEBUG
      fprintf (stdout, "mk_symbol: local %s (id %d)\n", name, ret->p.sid);
#endif
      return ret;
    }
  /* else, it shall be a field */
  if (name[0] == '?')
    {
      //fields cannot start with ?
      noll_error_id (1, "noll_mk_symbol", name);
      return NULL;
    }
  sid = noll_field_array_find (name);
  if (sid != UNDEFINED_ID)
    {
      ret = noll_mk_op (NOLL_F_FIELD, NULL, 0);
      ret->p.sid = sid;
      return ret;
    }
  /* else error */
  noll_error_id (1, "noll_mk_symbol", name);
  return NULL;
}

noll_exp_t *
noll_mk_pred (noll_context_t * ctx, const char *name, noll_exp_t ** args,
	      uint_t size)
{
  assert (name != NULL);
  assert (args != NULL);
  if (size < 2)
    {
      char *msg = strdup (name);
      noll_error_args (1, msg, size, ">= 2");
      free (msg);
      return NULL;
    }
  //search the predicate name
  uint_t pid = noll_pred_array_find (name);
  if (pid == UNDEFINED_ID)
    {
      //it is maybe a recursive definition
      if (ctx->pname != NULL)
	{
	  //but the second recursive call, not good
	  noll_error_id (1, "noll_mk_pred", name);
	  return NULL;
	}
      else if (noll_vector_size (ctx->lvar_stack) >= 3)
	//a predicate definition, fill pname
	ctx->pname = strdup (name);
    }
  //typechecking is done afterwards, build the expression
  noll_exp_t *res = noll_mk_op (NOLL_F_PRED, args, size);
  res->p.sid = pid;
  return res;
}

noll_exp_t *
noll_mk_true (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_TRUE;
  return res;
}

noll_exp_t *
noll_mk_false (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_FALSE;
  return res;
}

noll_exp_t *
noll_mk_and (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (size <= 0)
    /*
     * 0 arguments is
     * false
     */
    return noll_mk_false (ctx);
  else if (size == 1)
    return args[0];
  return noll_mk_op (NOLL_F_AND, args, size);
}

noll_exp_t *
noll_mk_or (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (size <= 0)
    /*
     * 0 arguments is
     * true
     */
    return noll_mk_true (ctx);
  else if (size == 1)
    return args[0];
  return noll_mk_op (NOLL_F_OR, args, size);
}

noll_exp_t *
noll_mk_not (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_not", size, "= 1");
  noll_exp_t *e = args[0];
  if (e->discr == NOLL_F_INLOC)
    {
      e->discr = NOLL_F_NILOC;
      return e;
    }
  else if (e->discr == NOLL_F_NILOC)
    {
      e->discr = NOLL_F_INLOC;
      return e;
    }
  else
    return noll_mk_op (NOLL_F_NOT, args, size);
}

noll_exp_t *
noll_mk_eq (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_eq", size, "= 2");
  return noll_mk_op (NOLL_F_EQ, args, size);
}

noll_exp_t *
noll_mk_distinct (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_distinct", size, "= 2");
  return noll_mk_op (NOLL_F_DISTINCT, args, size);
}

noll_exp_t *
noll_mk_emp (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_EMP;
  return res;
}

noll_exp_t *
noll_mk_junk (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_JUNK;
  return res;
}

noll_exp_t *
noll_mk_wsep (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_wsep", size, ">= 2");
  return noll_mk_op (NOLL_F_WSEP, args, size);
}

noll_exp_t *
noll_mk_ssep (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_ssep", size, ">= 2");
  return noll_mk_op (NOLL_F_SSEP, args, size);
}

noll_exp_t *
noll_mk_pto (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_pto", size, "= 2");
  return noll_mk_op (NOLL_F_PTO, args, size);
}

noll_exp_t *
noll_mk_ref (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mksref", size, ">= 2");
  return noll_mk_op (NOLL_F_REF, args, size);
}

noll_exp_t *
noll_mk_sref (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_sref", size, ">= 2");
  return noll_mk_op (NOLL_F_SREF, args, size);
}

noll_exp_t *
noll_mk_index (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_index", size, "= 2");
  return noll_mk_op (NOLL_F_INDEX, args, size);
}

noll_exp_t *
noll_mk_sloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_sloc", size, "= 1");
  return noll_mk_op (NOLL_F_SLOC, args, size);
}

noll_exp_t *
noll_mk_unloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_unloc", size, ">= 2");
  return noll_mk_op (NOLL_F_UNLOC, args, size);
}

noll_exp_t *
noll_mk_inloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_inloc", size, "= 2");
  return noll_mk_op (NOLL_F_INLOC, args, size);
}

noll_exp_t *
noll_mk_eqloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_eqloc", size, "= 2");
  return noll_mk_op (NOLL_F_EQLOC, args, size);
}

noll_exp_t *
noll_mk_leloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_leloc", size, "= 2");
  return noll_mk_op (NOLL_F_LELOC, args, size);
}

noll_exp_t *
noll_mk_seloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_seloc", size, "= 2");
  return noll_mk_op (NOLL_F_SELOC, args, size);
}

noll_exp_t *
noll_mk_tobool (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_tobool", size, "= 1");
  return noll_mk_op (NOLL_F_TOBOOL, args, size);
}

noll_exp_t *
noll_mk_tospace (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_tospace", size, "= 1");
  return noll_mk_op (NOLL_F_TOSPACE, args, size);
}

noll_exp_t *
noll_mk_loop (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_loop", size, "= 1");
  return noll_mk_op (NOLL_F_LOOP, args, size);
}

/*
 * ======================================================================
 * Printing
 * ======================================================================
 */

void
noll_exp_printf (FILE * f, noll_context_t * ctx, noll_exp_t * e)
{
  assert (f);
  if (!e)
    {
      fprintf (f, "null\n");
      return;
    }
  switch (e->discr)
    {
    case NOLL_F_FALSE:
      {
	fprintf (f, " false ");
	return;
      }
    case NOLL_F_TRUE:
      {
	fprintf (f, " true ");
	return;
      }
    case NOLL_F_LVAR:
      {
	fprintf (f, " %s ",
		 noll_var_name (ctx->lvar_env, e->p.sid, NOLL_TYP_RECORD));
	return;
      }
    case NOLL_F_SVAR:
      {
	fprintf (f, " %s ",
		 noll_var_name (ctx->svar_env, e->p.sid, NOLL_TYP_SETLOC));
	return;
      }
    case NOLL_F_FIELD:
      {
	fprintf (f, " %s ", noll_field_name (e->p.sid));
	return;
      }
    case NOLL_F_EMP:
      {
	fprintf (f, " emp ");
	return;
      }
    case NOLL_F_JUNK:
      {
	fprintf (f, " junk ");
	return;
      }
    case NOLL_F_NOT:
      {
	fprintf (f, " (not \n");
	break;
      }
    case NOLL_F_AND:
      {
	fprintf (f, " (and \n\t");
	break;
      }
    case NOLL_F_OR:
      {
	fprintf (f, " (or \n\t");
	break;
      }
    case NOLL_F_IMPLIES:
      {
	fprintf (f, " (implies \n\t");
	break;
      }
    case NOLL_F_EXISTS:
      {
	fprintf (f, " (exists (");
	for (uint_t i = e->p.quant.lstart; i < e->p.quant.lend; i++)
	  {
	    noll_var_t *vi = noll_vector_at (e->p.quant.lvars, i);
	    fprintf (f, " (%s %s) ", vi->vname,
		     noll_record_name (noll_var_record
				       (e->p.quant.lvars, i)));
	  }
	for (uint_t i = e->p.quant.sstart; i < e->p.quant.send; i++)
	  {
	    noll_var_t *vi = noll_vector_at (e->p.quant.svars, i);
	    fprintf (f, " (%s SetLoc) ", vi->vname);
	  }
	fprintf (f, " )\n\t");
	break;
      }
    case NOLL_F_PRED:
      {
	const char *pred_name = noll_pred_name (e->p.sid);
	assert (NULL != pred_name);
	fprintf (f, " (%s ", pred_name);
	break;
      }
    case NOLL_F_EQ:
      {
	fprintf (f, " (= ");
	break;
      }
    case NOLL_F_DISTINCT:
      {
	fprintf (f, " (distinct ");
	break;
      }
    case NOLL_F_WSEP:
      {
	fprintf (f, " (wsep \n\t");
	break;
      }
    case NOLL_F_SSEP:
      {
	fprintf (f, " (ssep \n\t");
	break;
      }
    case NOLL_F_PTO:
      {
	fprintf (f, " (pto ");
	break;
      }
    case NOLL_F_REF:
      {
	fprintf (f, " (ref ");
	break;
      }
    case NOLL_F_SREF:
      {
	fprintf (f, " (sref \n\t");
	break;
      }
    case NOLL_F_INDEX:
      {
	fprintf (f, " (index ");
	break;
      }
    case NOLL_F_SLOC:
      {
	fprintf (f, " (sloc ");
	break;
      }
    case NOLL_F_UNLOC:
      {
	fprintf (f, " (unloc ");
	break;
      }
    case NOLL_F_INLOC:
      {
	fprintf (f, " (inloc ");
	break;
      }
    case NOLL_F_NILOC:
      {
	fprintf (f, " (notinloc ");
	break;
      }
    case NOLL_F_EQLOC:
      {
	fprintf (f, " (eqloc ");
	break;
      }
    case NOLL_F_LELOC:
      {
	fprintf (f, " (leloc ");
	break;
      }
    case NOLL_F_SELOC:
      {
	fprintf (f, " (seloc ");
	break;
      }
    case NOLL_F_TOBOOL:
      {
	fprintf (f, " (tobool \n\t");
	break;
      }
    case NOLL_F_TOSPACE:
      {
	fprintf (f, " (tospace \n\t");
	break;
      }
    case NOLL_F_LOOP:
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
	  noll_exp_printf (f, ctx, e->args[i]);
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
noll_exp_t *
noll_exp_typecheck_and (noll_context_t * ctx, noll_exp_t * e)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (!e)
    return e;

  //top formulas shall be linked by and or tobool, expected type bool
  assert ((e->discr == NOLL_F_AND) || (e->discr == NOLL_F_TOBOOL));
  //TODO
  return e;
}

/**
 * Typechecks an EXISTS formula.
 */
noll_exp_t *
noll_exp_typecheck_exists (noll_context_t * ctx, noll_exp_t * e)
{
  if (!e)
    return e;
  if (e->discr == NOLL_F_EXISTS)
    {
      //top formula shall non be empty, expected type bool
      assert (e->size == 1);
      e->args[0] = noll_exp_typecheck_and (ctx, e->args[0]);
      if (!e->args[0])
	return NULL;
      return e;
    }
  return noll_exp_typecheck_and (ctx, e);
}

/** Typechecks the expression and simplifies it.
 *  Expected type is boolean at the top level.
 * @param ctx  context with global variables
 * @param e    formula to be typechecked
 * @return the new (simplified) formula
 */
noll_exp_t *
noll_exp_typecheck (noll_context_t * ctx, noll_exp_t * e)
{
  if (!e)
    return e;

  switch (e->discr)
    {
    case NOLL_F_TRUE:
    case NOLL_F_FALSE:
      return e;
    case NOLL_F_NOT:
      {
	assert (e->size == 1);
	noll_exp_t *se = noll_exp_typecheck_exists (ctx, e->args[0]);
	if (se == NULL)
	  return NULL;
	e->args[0] = se;
	return e;
      }
    case NOLL_F_TOBOOL:
    case NOLL_F_AND:
      return noll_exp_typecheck_and (ctx, e);
    case NOLL_F_IMPLIES:
      {
	assert (e->size == 2);
	//done in mk_implies
	e->args[0] = noll_exp_typecheck_exists (ctx, e->args[0]);
	e->args[1] = noll_exp_typecheck_exists (ctx, e->args[1]);
	if (!e->args[0] || !e->args[1])
	  return NULL;
	return e;
      }
    case NOLL_F_EXISTS:
      {
	return noll_exp_typecheck_exists (ctx, e);
      }
    default:
      {
	noll_error (0, "noll_exp_typecheck", "syntax error in formula");
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
noll_exp_push_pure (noll_context_t * ctx, noll_exp_t * e, noll_form_t * form)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  assert (e);

  if (form->pure == NULL)
    form->pure = noll_pure_new (noll_vector_size (form->lvars));
  switch (e->discr)
    {
    case NOLL_F_EQ:
      {
	//the variables implied in the equality
	uint_t v1 = e->args[0]->p.sid;
	uint_t v2 = e->args[1]->p.sid;
	noll_pure_add_eq (form, v1, v2);
	break;
      }
    case NOLL_F_DISTINCT:
      {
	//the variables implied in the equality
	uint_t v1 = e->args[0]->p.sid;
	uint_t v2 = e->args[1]->p.sid;
	noll_pure_add_neq (form, v1, v2);
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
noll_space_t *
noll_mk_form_junk (noll_exp_t * f)
{
  assert (f && f->discr == NOLL_F_JUNK);
  noll_space_t *sigma = (noll_space_t *) malloc (sizeof (noll_space_t));
  sigma->kind = NOLL_SPACE_JUNK;
  sigma->is_precise = (f != NULL) ? false : true;
  return sigma;
}

/**
 * Translates the AST in e to a points-to space formula.
 * @param env  formula containing the environment of variables used
 * @param f the AST of the points-to formula
 * @return the space formula or NULL of error
 */
noll_space_t *
noll_mk_form_pto (noll_context_t * ctx, noll_exp_t * f)
{
  assert (f && f->discr == NOLL_F_PTO && f->size == 2);
  noll_exp_t *v = f->args[0];
  noll_exp_t **fv = NULL;
  uint_t fv_size = 1;
  noll_space_t *sigma = (noll_space_t *) malloc (sizeof (noll_space_t));
  sigma->kind = NOLL_SPACE_PTO;
  sigma->is_precise = true;

  if (v->discr == NOLL_F_LVAR)
    sigma->m.pto.sid = v->p.sid;
  //is in context

  // fill the set of locations from fv which may be ref or sref
  if (f->args[1]->discr == NOLL_F_REF)
    {
      fv_size = 1;
      fv = &f->args[1];
    }
  else if (f->args[1]->discr == NOLL_F_SREF)
    {
      fv_size = f->args[1]->size;
      fv = f->args[1]->args;
    }
  else
    {
      noll_error (1, "Building points-to formula: bad type for location ",
		  noll_var_name (ctx->lvar_env, v->p.sid, NOLL_TYP_RECORD));
      noll_space_free (sigma);
      return NULL;
    }
  sigma->m.pto.dest = noll_uid_array_new ();
  noll_uid_array_reserve (sigma->m.pto.dest, fv_size);
  sigma->m.pto.fields = noll_uid_array_new ();
  noll_uid_array_reserve (sigma->m.pto.fields, fv_size);
  uint_t i;
  for (i = 0; i < fv_size; i++)
    {
      assert (fv[i]->discr == NOLL_F_REF && fv[i]->size == 2);
      uint_t dest = UNDEFINED_ID;
      if (fv[i]->args[1]->discr == NOLL_F_LVAR)
	dest = fv[i]->args[1]->p.sid;
      else
	assert (0);
      assert (fv[i]->args[0]->discr == NOLL_F_FIELD);
      uint_t fld = fv[i]->args[0]->p.sid;
      // because the term has been built
      assert (fld != UNDEFINED_ID);
      // notice that we may have dest == UNDEFINED_ID == VNIL_ID
      noll_uid_array_push (sigma->m.pto.dest, dest);
      noll_uid_array_push (sigma->m.pto.fields, fld);
    }
  return sigma;
}

noll_space_t *
noll_mk_form_loop (noll_context_t * ctx, noll_exp_t * e)
{
  noll_space_t *ret = NULL;
  assert (e && e->discr == NOLL_F_LOOP);
  //there is only one argument
  if (e->size != 1)
    {
      noll_error (1, "Loop expression", "bad number of arguments");
      return ret;
    }
  //generate the argument which shall be a predicate call
  if (e->args[0]->discr != NOLL_F_PRED)
    {
      noll_error (1, "Loop expression", "bad predicate argument");
      return ret;
    }
  ret = noll_mk_form_pred (ctx, e->args[0]);
  if (ret != NULL)
    {
      /* if no error, set loop in the predicate call */
      ret->m.ls.is_loop = true;
    }
  return ret;
}

noll_space_t *
noll_mk_form_pred (noll_context_t * ctx, noll_exp_t * e)
{
  assert (e && e->discr == NOLL_F_PRED && e->size >= 2);
  //check that the type of actual arguments is correct
  noll_uid_array *actuals = noll_uid_array_new ();
  noll_uid_array_reserve (actuals, e->size);
  uint_t *actuals_ty = (uint_t *) malloc (e->size * sizeof (uint_t));
  const char *pname = noll_pred_name (e->p.sid);
  assert (NULL != pname);
  uint_t i;
  for (i = 0; i < e->size; i++)
    {
      if (e->args[i]->discr != NOLL_F_LVAR || e->args[i]->size != 0)
	{
	  noll_error (1, "Predicate call to ", pname);
	  noll_error (1, "Bad (last) parameters.", "");
	  free (actuals);
	  free (actuals_ty);
	  return NULL;
	}
      uint_t pi = e->args[i]->p.sid;
      noll_uid_array_push (actuals, pi);
      actuals_ty[i] = noll_var_record (ctx->lvar_env, pi);
    }
  uint_t pid = noll_pred_typecheck_call (e->p.sid, actuals_ty, e->size);
  free (actuals_ty);

  //generate the corresponding space formula
  noll_space_t *pcall = (noll_space_t *) malloc (sizeof (noll_space_t));
  pcall->kind = NOLL_SPACE_LS;
  pcall->is_precise = true;
  pcall->m.ls.pid = pid;
  pcall->m.ls.args = actuals;
  pcall->m.ls.sid = UNDEFINED_ID;
  pcall->m.ls.is_loop = false;
  //pcall->m.ls.sid is set in INDEX

  return pcall;
}

noll_space_t *
noll_mk_form_index (noll_context_t * ctx, noll_exp_t * e)
{
  noll_space_t *ret = NULL;
  assert (e && e->discr == NOLL_F_INDEX);
  //there are two arguments only
  if (e->size != 2)
    {
      noll_error (1, "Index expression", "bad number of arguments");
      return ret;
    }
  //first argument is a variable, get its id
  uint_t sid = UNDEFINED_ID;
  if (e->args[0]->discr == NOLL_F_SVAR)
    sid = e->args[0]->p.sid;
  if (sid == UNDEFINED_ID)
    {
      noll_error (1, "Index expression", "bad variable argument");
      return ret;
    }
  //generate the second argument which shall be a predicate call
  //with maybe a loop
  if ((e->args[1]->discr != NOLL_F_PRED) &&
      (e->args[1]->discr != NOLL_F_LOOP))
    {
      noll_error (1, "Index expression", "bad predicate argument");
      return ret;
    }
  if (e->args[1]->discr == NOLL_F_PRED)
    ret = noll_mk_form_pred (ctx, e->args[1]);
  else
    ret = noll_mk_form_loop (ctx, e->args[1]);

  if (ret != NULL)
    {
      /* if no error, bound sid to the predicate call */
      ret->m.ls.sid = sid;
    }
  return ret;
}

noll_space_t *
noll_mk_form_sep (noll_context_t * ctx, noll_exp_t * e)
{
  noll_space_t *ret = NULL;
  assert (e && (e->discr == NOLL_F_SSEP || e->discr == NOLL_F_WSEP));

  //allocate the space formula
  ret = (noll_space_t *) malloc (sizeof (noll_space_t));
  ret->kind = (e->discr == NOLL_F_SSEP) ? NOLL_SPACE_SSEP : NOLL_SPACE_WSEP;
  ret->is_precise = true;
  ret->m.sep = noll_space_array_new ();
  //reserve at least the number of arguments here
  noll_space_array_reserve (ret->m.sep, e->size);
  for (uint_t i = 0; i < e->size; i++)
    {
      noll_space_t *ei = noll_exp_push_space (ctx, e->args[i]);
      if (ei == NULL)
	continue;
      //is_precise attribute is propagated to parents
      if (ei->is_precise == false)
	ret->is_precise = false;
      if (ei->kind == ret->kind)
	{
	  //same separation operator, remove the intermediary node
	  for (uint_t j = 0; j < noll_vector_size (ei->m.sep); j++)
	    {
	      noll_space_t *eij = noll_vector_at (ei->m.sep, j);
	      noll_space_array_push (ret->m.sep, eij);
	      noll_vector_at (ei->m.sep, j) = NULL;
	    }
	  noll_space_array_delete (ei->m.sep);
	  free (ei);
	}
      else
	{
	  //different operator, push the formula as arguments
	  noll_space_array_push (ret->m.sep, ei);
	}
    }
  return ret;
}

noll_space_t *
noll_exp_push_space (noll_context_t * ctx, noll_exp_t * e)
{
  assert (e);

  noll_space_t *ret = NULL;
  switch (e->discr)
    {
    case NOLL_F_EMP:
      /* nothing */
      break;
    case NOLL_F_JUNK:
      {
	ret = noll_mk_form_junk (e);
	break;
      }
    case NOLL_F_PTO:
      {
	ret = noll_mk_form_pto (ctx, e);
	break;
      }
    case NOLL_F_PRED:
      {
	ret = noll_mk_form_pred (ctx, e);
	break;
      }
    case NOLL_F_INDEX:
      {
	ret = noll_mk_form_index (ctx, e);
	break;
      }
    case NOLL_F_WSEP:
    case NOLL_F_SSEP:
      {
	ret = noll_mk_form_sep (ctx, e);
	break;
      }
    default:
      noll_error (1, "noll_exp_push_space", "not a space formula");
      break;
    }
  return ret;
}

void
noll_exp_push_sterm (noll_exp_t * e, noll_sterm_array * a)
{
  assert (e);
  if (!(e->discr == NOLL_F_SLOC || e->discr == NOLL_F_UNLOC
	|| e->discr == NOLL_F_SELOC || e->discr == NOLL_F_SVAR))
    {
      noll_error (1, "noll_exp_push_sterm",
		  "not a term for sets of locations");
      return;
    }
  switch (e->discr)
    {
    case NOLL_F_SLOC:
      {
	assert (e->args[0] && e->args[0]->discr == NOLL_F_LVAR);
	noll_sterm_t *tv = noll_sterm_new_var (e->args[0]->p.sid,
					       NOLL_STERM_LVAR);
	noll_sterm_array_push (a, tv);
	break;
      }
    case NOLL_F_SVAR:
      {
	noll_sterm_t *tv = noll_sterm_new_var (e->p.sid, NOLL_STERM_SVAR);
	noll_sterm_array_push (a, tv);
	break;
      }
    case NOLL_F_SELOC:
      {
	assert (e->args[0] && e->args[0]->discr == NOLL_F_SVAR);
	assert (e->args[1] && e->args[1]->discr == NOLL_F_LVAR);
	noll_sterm_t *tv = noll_sterm_new_prj (e->args[0]->p.sid,
					       e->args[1]->p.sid);
	noll_sterm_array_push (a, tv);
	break;
      }
    default:
      //NOLL_F_UNLOC:
      {
	for (uint_t i = 0; i < e->size; i++)
	  noll_exp_push_sterm (e->args[i], a);
	break;
      }
    }
}

void
noll_exp_push_share (noll_context_t * ctx, noll_exp_t * e, noll_form_t * form)
{
  assert (e && e->size == 2);

  switch (e->discr)
    {
    case NOLL_F_NILOC:
    case NOLL_F_INLOC:
      {
	noll_atom_share_t *a =
	  (noll_atom_share_t *) malloc (sizeof (noll_atom_share_t));
	a->kind = (e->discr == NOLL_F_INLOC) ? NOLL_SHARE_IN : NOLL_SHARE_NI;
	assert (e->args[0]);
	assert (e->args[0]->discr == NOLL_F_LVAR);
	noll_sterm_t *tv = noll_sterm_new_var (e->args[0]->p.sid,
					       NOLL_STERM_LVAR);
	a->t_left = tv;
	a->t_right = noll_sterm_array_new ();
	noll_exp_push_sterm (e->args[1], a->t_right);
	noll_share_array_push (form->share, a);
	break;
      }
    case NOLL_F_EQLOC:
      {
	//push conjunct for <=
	e->discr = NOLL_F_LELOC;
	noll_exp_push_share (ctx, e, form);
	//push conjunct for >=
	noll_exp_t *tmp = e->args[0];
	e->args[0] = e->args[1];
	e->args[1] = tmp;
	noll_exp_push_share (ctx, e, form);
	//redo the expression
	e->discr = NOLL_F_EQLOC;
	tmp = e->args[0];
	e->args[0] = e->args[1];
	e->args[1] = tmp;
	break;
      }
    case NOLL_F_LELOC:
      {
	noll_sterm_array *left = noll_sterm_array_new ();
	noll_exp_push_sterm (e->args[0], left);
	noll_sterm_array *right = noll_sterm_array_new ();
	noll_exp_push_sterm (e->args[1], right);
	for (uint_t i = 0; i < noll_vector_size (left); i++)
	  {
	    noll_atom_share_t *a =
	      (noll_atom_share_t *) malloc (sizeof (noll_atom_share_t));
	    a->kind = NOLL_SHARE_SUBSET;
	    a->t_left = noll_vector_at (left, i);
	    a->t_right = right;
	    noll_share_array_push (form->share, a);
	  }
	break;
      }
    default:
      {
	noll_error (1, "noll_exp_push_share", "not a sharing constraint");
	break;
      }
    }
}

void
noll_exp_push_top (noll_context_t * ctx, noll_exp_t * e, noll_form_t * form)
{
  assert (ctx != NULL);
  assert (e != NULL);
  assert (form != NULL);

  if (form->kind == NOLL_FORM_UNSAT)
    return;

  //copy variables from context to formula
  if (form->lvars != NULL && form->lvars != ctx->lvar_env)
    noll_var_array_delete (form->lvars);
  form->lvars = ctx->lvar_env;
  if (form->svars != NULL && form->svars != ctx->svar_env)
    noll_var_array_delete (form->svars);
  form->svars = ctx->svar_env;
#ifndef NDEBUG
  fprintf (stdout, "\nnoll_exp_push_top:\n\t");
  noll_var_array_fprint (stdout, form->lvars, "lvars");
  fprintf (stdout, "\n\t");
  noll_var_array_fprint (stdout, form->svars, "svars");
  fprintf (stdout, "\n");
#endif
  //fill other parts of the formula
  switch (e->discr)
    {
      /* boolean operations */
    case NOLL_F_TRUE:
      return;			/* nothing to be done */
    case NOLL_F_FALSE:
      {
	/*
	 * set the formula to unsat
	 */
	noll_form_set_unsat (form);
	break;
      }
    case NOLL_F_AND:
      {
	for (uint_t i = 0; i < e->size; i++)
	  noll_exp_push_top (ctx, e->args[i], form);
	break;
      }
    case NOLL_F_EXISTS:
      {
	//existential variables are already in form->? vars
	for (uint_t i = 0; i < e->size; i++)
	  noll_exp_push_top (ctx, e->args[i], form);
	break;
      }
    case NOLL_F_NOT:
    case NOLL_F_OR:
    case NOLL_F_IMPLIES:
    case NOLL_F_FORALL:
      {
	//this is an error, no translation is possible
	noll_error (0, "noll_exp_push_top", "boolean operation not allowed");
	return;
      }

      /* pure constraints */
    case NOLL_F_EQ:
    case NOLL_F_DISTINCT:
      {
#ifndef NDEBUG
	fprintf (stdout, "Push pure:");
	noll_exp_printf (stdout, ctx, e);
	fflush (stdout);
#endif
	noll_exp_push_pure (ctx, e, form);
	break;
      }
      /*
       * towards space
       * operations
       */
    case NOLL_F_TOBOOL:
      {
	form->space = noll_exp_push_space (ctx, e->args[0]);
	if (form->kind == NOLL_FORM_VALID && form->space != NULL)
	  form->kind = NOLL_FORM_SAT;
	//over - approximate
	break;
      }
      /* share operators */
    case NOLL_F_INLOC:
    case NOLL_F_NILOC:
    case NOLL_F_EQLOC:
    case NOLL_F_LELOC:
      {
	if (!form->share)
	  form->share = noll_share_array_new ();
	noll_exp_push_share (ctx, e, form);
	if (form->kind == NOLL_FORM_VALID && form->share != NULL)
	  form->kind = NOLL_FORM_SAT;
	//over - approximate
	break;
      }
    case NOLL_F_SELOC:
    case NOLL_F_SLOC:
    case NOLL_F_UNLOC:
      {
	//this is an error, no translation is possible
	noll_error (0, "noll_exp_push_top", "set operation not allowed");
	return;
      }
    default:
      {
	//this is an error, no translation is possible
	noll_error (0, "noll_exp_push_top", "space operation not allowed");
	return;
      }
    }
}

/** Translation form AST to NOLL formula and push into the global formulas.
 */
void
noll_exp_push (noll_context_t * ctx, noll_exp_t * e, int ispos)
{
#ifndef NDEBUG
  //printing now:
  fprintf (stdout, "Push %stive formula:\n", (ispos) ? "posi" : "nega");
  noll_exp_printf (stdout, ctx, e);
  fprintf (stdout, "\nwith context: ");
  noll_var_array_fprint (stdout, ctx->lvar_env, "lvars");
  noll_var_array_fprint (stdout, ctx->svar_env, "svars");
  fflush (stdout);
#endif
  if (!e)
    return;

  noll_form_t *form =
    (ispos == 0) ? noll_entl_get_nform_last () : noll_entl_get_pform ();

  /* if unsat formula, no need to push more formulas */
  if (form->kind == NOLL_FORM_UNSAT)
    return;

  noll_exp_push_top (ctx, e, form);

  return;
}
