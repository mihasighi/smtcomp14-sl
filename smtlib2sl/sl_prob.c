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

/**
 * Defines the problem for the decision procedure.
 */

#include <sys/time.h>
#include <stdio.h>

#include "sl.h"
#include "sl_form.h"
#include "sl_prob.h"

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

sl_prob_t *sl_prob;		// problem of entailment in sl

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialization/Deallocation of problem */
void
sl_prob_init ()
{
  sl_prob = (sl_prob_t *) malloc (sizeof (sl_prob_t));
  // init file name
  sl_prob->smt_fname = NULL;

  // init fst pred
  sl_prob->fst_pid = UNDEFINED_ID;

  // init positive formula
  sl_prob->pform = sl_form_new ();

  // init negative formulae array
  sl_prob->nform = sl_form_array_new ();

  // init command
  sl_prob->cmd = SL_PROB_SAT;	// by default value
}

void
sl_prob_free (void)
{
  assert (sl_prob != NULL);
  // this procedure shall be called only once
  if (sl_prob->smt_fname != NULL)
    {
      free (sl_prob->smt_fname);
      sl_prob->smt_fname = NULL;
    }
  if (sl_prob->pform != NULL)
    {
      sl_form_free (sl_prob->pform);
      sl_prob->pform = NULL;
    }
  if (sl_prob->nform != NULL)
    {
      sl_form_array_delete (sl_prob->nform);
      sl_prob->nform = NULL;
    }
  free (sl_prob);
}

/* ====================================================================== */
/* Getters */
/* ====================================================================== */

sl_form_t *
sl_prob_get_pform ()
{
  assert (sl_prob != NULL);
  return sl_prob->pform;
}

sl_form_t *
sl_prob_get_nform_last ()
{
  assert (sl_prob != NULL);
  if (sl_vector_empty (sl_prob->nform))
    sl_form_array_push (sl_prob->nform, sl_form_new ());
  return sl_vector_last (sl_prob->nform);
}

/* ====================================================================== */
/* Setters */
/* ====================================================================== */

void
sl_prob_set_fname (char *fname)
{
  assert (sl_prob->smt_fname == NULL);
  sl_prob->smt_fname = fname;
}

void
sl_prob_set_cmd (sl_prob_kind_t pb)
{
  sl_prob->cmd = pb;
}

void
sl_prob_set_pid (uid_t pid)
{
  if (sl_prob->fst_pid == UNDEFINED_ID)
    sl_prob->fst_pid = pid;
}


/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void
sl_prob_fprint (FILE * f)
{
  assert (f != NULL);

  if (sl_prob == NULL)
    {
      fprintf (f, "*** (problem) null\n");
      return;
    }

  fprintf (f, "*** (source %s) check-%s on:\n", sl_prob->smt_fname,
	   (sl_prob->cmd == SL_PROB_SAT) ? "sat" : "unsat");

  sl_records_array_fprint (f, "records:");
  sl_fields_array_fprint (f, "fields:");
  fprintf (f, "\nEntry predicate: %s\n", sl_pred_name(sl_prob->fst_pid));
  sl_pred_array_fprint (f, preds_array, "predicates:");

  fprintf (f, "\nPositive formula: ");
  sl_form_fprint (f, sl_prob->pform);
  fflush (f);
  fprintf (f, "\nNegative formulas: ");
  if (sl_vector_empty (sl_prob->nform))
    fprintf (f, "[]\n");
  else
    {
      for (size_t i = 0; i < sl_vector_size (sl_prob->nform); i++)
	{
	  fprintf (f, "\n\\/ (0-%zu): ", i);
	  sl_form_fprint (f, sl_vector_at (sl_prob->nform, i));
	}
      fprintf (f, "\n");
    }
  fflush (stdout);
}

/* ====================================================================== */
/* Typechecking */
/* ====================================================================== */

/**
 * Type the predicates, fields, formulas in sl_prob.
 * @return 1 if typing is ok
 */
int
sl_prob_type ()
{
  /*
   * Type predicate definitions,
   * it has side effects on the typing infos on preds_array 
   */
  if (sl_pred_type () == 0)
    return 0;

  /*
   * Type formulas inside the problem.
   */
  if (sl_form_type (sl_prob->pform) == 0)
    return 0;

  for (uint_t i = 0; i < sl_vector_size (sl_prob->nform); i++)
    if (sl_form_type (sl_vector_at (sl_prob->nform, i)) == 0)
      {
#ifndef NDEBUG
	fprintf (stdout, "*** sl_prob_type: type error in %d nform.\n", i);
	fflush (stdout);
#endif
	return 0;
      }

  return 1;
}
