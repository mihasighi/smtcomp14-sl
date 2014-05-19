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
 * Translation to the Cyclist format
 */

#include <sys/time.h>
#include <stdio.h>

#include "sl.h"
#include "sl_form.h"
#include "sl_prob.h"
#include "sl_prob2cyclist.h"


/* ====================================================================== */
/* Vars */
/* ====================================================================== */

char *
sl_var_2cyclist (sl_var_array * args, sl_var_array * lvars, uid_t vid)
{

  char *vname;
  uid_t fstlocal = (args == NULL) ? 0 : sl_vector_size (args);
  if (vid >= fstlocal)
    {
      vname = sl_var_name (lvars, vid - fstlocal, SL_TYP_RECORD);
    }
  else
    vname = sl_var_name (args, vid, SL_TYP_RECORD);
  return (vname[0] == '?') ? vname + 1 : vname;
}


void
sl_var_array_2cyclist (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		       sl_uid_array * va)
{

  for (size_t i = 0; i < sl_vector_size (va); i++)
    {
      if (i > 0)
	fprintf (fout, ",");
      fprintf (fout, "%s", sl_var_2cyclist (args, lvars,
					    sl_vector_at (va, i)));
    }
}

/* ====================================================================== */
/* Formula */
/* ====================================================================== */

void
sl_pure_2cyclist (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		  sl_pure_t * form)
{
  assert (NULL != form);

  // shall always start by the local vars
  char *vleft = sl_var_2cyclist (args, lvars, form->vleft);

  char *vright = sl_var_2cyclist (args, lvars, form->vright);

  fprintf (fout, "%s%s%s", vleft,
	   (form->op == SL_PURE_EQ) ? "=" : "!=", vright);
}

void
sl_space_2cyclist (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		   sl_space_t * form)
{

  assert (NULL != form);

  // Only pto and ls are allowed, all precise
  switch (form->kind)
    {
    case SL_SPACE_PTO:
      {
	// print source
	fprintf (fout, "%s->",
		 sl_var_2cyclist (args, lvars, form->m.pto.sid));
	// print destinations
	sl_var_array_2cyclist (fout, args, lvars, form->m.pto.dest);

	break;
      }

    case SL_SPACE_LS:
      {
	// print predicate
	fprintf (fout, "%s(", sl_pred_name (form->m.ls.pid));
	// print arguments
	sl_var_array_2cyclist (fout, args, lvars, form->m.ls.args);
	fprintf (fout, ")");
	break;
      }

    default:
      {
	sl_error (1, "sl_space_2cyclist:", "spatial formula not LS or PTO");
      }
    }
}

void
sl_form_2cyclist (FILE * fout, sl_form_t * form)
{
  assert (NULL != fout);
  assert (NULL != form);

  size_t nbc = 0;

  // start with pure formula
  for (size_t i = 0; i < sl_vector_size (form->pure); i++)
    {
      if (nbc > 0)
	fprintf (fout, " * ");
      sl_pure_2cyclist (fout, NULL, form->lvars,
			sl_vector_at (form->pure, i));
      fflush (fout);
      nbc++;
    }

  if (form->space == NULL)
    return;

  // continue with spatial formulas
  // Only ssep atomic formulas
  switch (form->space->kind)
    {
    case SL_SPACE_PTO:
    case SL_SPACE_LS:
      {

	if (nbc > 0)
	  fprintf (fout, " * ");
	sl_space_2cyclist (fout, NULL, form->lvars, form->space);
	nbc++;
	break;
      }
    case SL_SPACE_SSEP:
      {
	for (size_t i = 0; i < sl_vector_size (form->space->m.sep); i++)
	  {
	    if (nbc > 0)
	      fprintf (fout, " * ");
	    sl_space_2cyclist (fout, NULL, form->lvars,
			       sl_vector_at (form->space->m.sep, i));
	    fflush (fout);
	    nbc++;
	  }
	break;
      }
    default:
      {
	sl_error (1, "sl_form_2cyclist:", "not a PTO, LS, SSEP formula");
	return;
      }
    }
}

/* ====================================================================== */
/* Predicate */
/* ====================================================================== */
void
sl_pred_case_2cyclist (FILE * fout, sl_var_array * args, sl_pred_case_t * c)
{
  assert (NULL != fout);
  assert (NULL != args);
  assert (NULL != c);

  size_t nbc = 0;

  // start with pure formula
  for (size_t i = 0; i < sl_vector_size (c->pure); i++)
    {
      if (nbc > 0)
	fprintf (fout, " * ");
      sl_pure_2cyclist (fout, args, c->lvars, sl_vector_at (c->pure, i));
      fflush (fout);
      nbc++;
    }

  // continue with spatial formulas
  for (size_t i = 0; i < sl_vector_size (c->space); i++)
    {
      if (nbc > 0)
	fprintf (fout, " * ");
      sl_space_2cyclist (fout, args, c->lvars, sl_vector_at (c->space, i));
      fflush (fout);
      nbc++;
    }

  SL_DEBUG ("\t nbc=%zu\n", nbc);
  assert (nbc > 0);

}

void
sl_pred_2cyclist (FILE * fout, sl_pred_t * p)
{

  assert (NULL != fout);
  assert (NULL != p);

  fprintf (fout, "\n%s {\n  ", p->pname);

  SL_DEBUG ("Defs %s ...\n", p->pname);

  // Print all cases
  for (size_t i = 0; i < sl_vector_size (p->def->cases); i++)
    {
      // print separator
      if (i > 0)
	fprintf (fout, " |\n  ");
      // print formula
      sl_pred_case_2cyclist (fout, p->def->args,
			     sl_vector_at (p->def->cases, i));
      // print predicate instance
      fprintf (fout, " => %s(", p->pname);
      for (size_t vi = 1; vi <= p->def->argc; vi++)
	{
	  if (vi > 1)
	    fprintf (fout, ",");
	  fprintf (fout, "%s", sl_var_2cyclist (NULL, p->def->args, vi));
	}
      fprintf (fout, ")");
    }

  fprintf (fout, "\n} ");
}


/* ====================================================================== */
/* Problem */
/* ====================================================================== */
void
sl_prob_2cyclist (const char *fname)
{

  assert (NULL != fname);
  assert (sl_prob != NULL);

  sl_message ("*** Translation to Cyclist");

  /* Output filename */
  char *fname_out = (char *) malloc (strlen (fname) + 10);
  snprintf (fname_out, strlen (fname) + 10, "%s.defs", fname);

  /* Output file */
  sl_message ("\tOutput file: ");
  sl_message (fname_out);
  FILE *fout = fopen (fname_out, "w");
  if (!fout)
    {
      printf ("Can not create file '%s'!\nquit.", fname_out);
      return;
    }

  // Translates predicates
  size_t last = sl_vector_size (preds_array) - 1;
  for (size_t i = 0; i <= last; i++)
    {
      sl_pred_2cyclist (fout, sl_vector_at (preds_array, i));
      if (i < last)
	fprintf (fout, ";\n");
    }

  // Translated the problem only for entailment
  if (!sl_vector_empty (sl_prob->nform))
    {

      fprintf (fout, ";\n\n");

      // translate positive formula
      sl_form_2cyclist (fout, sl_prob->pform);

      fprintf (fout, " |- ");

      // translate negative formula
      sl_form_2cyclist (fout, sl_vector_at (sl_prob->nform, 0));
    }

  fclose (fout);

  sl_message ("\nDone\n");
}
