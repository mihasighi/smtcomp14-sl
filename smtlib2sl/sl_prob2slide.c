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
 * Translation to the Slide format
 */

#include <sys/time.h>
#include <stdio.h>

#include "sl.h"
#include "sl_form.h"
#include "sl_prob.h"
#include "sl_prob2slide.h"


/* ====================================================================== */
/* Vars */
/* ====================================================================== */

char *
sl_var_2slide (sl_var_array * args, sl_var_array * lvars, uid_t vid)
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
sl_vid_array_2slide (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		     sl_uid_array * va)
{

  for (size_t i = 0; i < sl_vector_size (va); i++)
    {
      if (i > 0)
	fprintf (fout, ",");
      fprintf (fout, "%s", sl_var_2slide (args, lvars, sl_vector_at (va, i)));
    }
}


/* ====================================================================== */
/* Formula */
/* ====================================================================== */

int
sl_pure_2slide (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		sl_pure_t * form)
{
  assert (NULL != form);

  // shall always start by the local vars
  char *vleft = sl_var_2slide (args, lvars, form->vleft);

  char *vright = sl_var_2slide (args, lvars, form->vright);

  fprintf (fout, "%s%s%s", vleft,
	   (form->op == SL_PURE_EQ) ? "=" : "!=", vright);
  return 1;
}

int
sl_ls_2slide (FILE * fout, sl_var_array * args, sl_var_array * lvars,
	      sl_space_t * form, bool errpto, bool withsep)
{

  assert (NULL != fout);
  assert (NULL != form);

  int nbc = 0;

  switch (form->kind)
    {
    case SL_SPACE_PTO:
      {
	if (errpto)
	  sl_error (1, "sl_ls_2slide", "PTO formula not allowed!\n");
	return 0;
      }
    case SL_SPACE_LS:
      {
	if (withsep)
	  fprintf (fout, " * ");
	// print predicate
	fprintf (fout, "%s(", sl_pred_name (form->m.ls.pid));
	// print arguments
	sl_vid_array_2slide (fout, args, lvars, form->m.ls.args);
	fprintf (fout, ")");
	nbc++;
	break;
      }
    case SL_SPACE_SSEP:
      {
	for (size_t i = 0; i < sl_vector_size (form->m.sep); i++)
	  {
	    int nls = sl_ls_2slide (fout, NULL, lvars,
				    sl_vector_at (form->m.sep, i), errpto,
				    (nbc > 0) ? true : withsep);
	    if (errpto && (nls == 0))
	      return 0;
	    fflush (fout);
	    nbc += nls;
	  }
	break;
      }
    default:
      {
	sl_error (1, "sl_form_2slide", "not a LS or SSEP formula");
	return 0;
      }
    }
  return nbc;
}

/**
 * Called in predicates for separated pto.
 */
int
sl_pto_2slide (FILE * fout, sl_var_array * args, sl_var_array * lvars,
	       sl_space_t * form, bool withsep)
{
  assert (NULL != form);

  // Only pto are allowed
  if (form->kind != SL_SPACE_PTO)
    {
      return 0;
    }

  if (withsep)
    fprintf (fout, " * ");

  // print source
  fprintf (fout, "%s->", sl_var_2slide (args, lvars, form->m.pto.sid));
  // print destinations
  sl_vid_array_2slide (fout, args, lvars, form->m.pto.dest);

  return 1;

}

/**
 * Only separated calls to predicats allowed.
 * @return 0 if not supported formula, 1 otherwise
 */
int
sl_form_2slide (FILE * fout, sl_form_t * form)
{
  assert (NULL != fout);
  assert (NULL != form);

  size_t nbc = 0;

  // existential vars are optional
  /*
     if (!sl_vector_empty(form->lvars)) {
     fprintf (fout, "\\E ");
     sl_var_array_2slide(fout, form->lvars, 1);
     fprintf (fout, " . ");
     }
   */

  // if pure formula, stop
  if (!sl_vector_empty (form->pure))
    return 0;

  if (form->space == NULL)
    {
      fprintf (fout, " emp\n");
      return 1;
    }

  // continue with spatial formulas
  // only LS formulas
  if (!sl_ls_2slide (fout, NULL, form->lvars, form->space, false, false))
    return 0;

  return 1;
}

/* ====================================================================== */
/* Predicate */
/* ====================================================================== */

int
sl_pred_case_2slide (FILE * fout, sl_var_array * args, sl_pred_case_t * c)
{
  assert (NULL != fout);
  assert (NULL != args);
  assert (NULL != c);

  size_t nbc = 0;

  // print existentials
  if (c->lvars != NULL && !sl_vector_empty (c->lvars))
    {
      fprintf (fout, "\\E ");
      for (size_t i = 0; i < sl_vector_size (c->lvars); i++)
	{
	  if (i > 0)
	    fprintf (fout, ",");
	  fprintf (fout, "%s",
		   sl_var_2slide (args, c->lvars, sl_vector_size (args) + i));
	}
      fprintf (fout, " . ");
    }

  // start with pto formula (only one!)
  for (size_t i = 0; i < sl_vector_size (c->space); i++)
    {
      nbc += sl_pto_2slide (fout, args, c->lvars, sl_vector_at (c->space, i),
			    (nbc > 0) ? true : false);
      fflush (fout);
    }

  if (nbc > 1)
    {
      sl_warning ("sl_pred_case_2slide",
		  "more than one pto in predicate definition");
      //return 0;
    }

  // continue with pure formula
  for (size_t i = 0; i < sl_vector_size (c->pure); i++)
    {
      if (nbc > 0)
	fprintf (fout, " & ");
      nbc += sl_pure_2slide (fout, args, c->lvars, sl_vector_at (c->pure, i));
      fflush (fout);
    }

  // continue with ls formulas
  for (size_t i = 0; i < sl_vector_size (c->space); i++)
    {
      nbc +=
	sl_ls_2slide (fout, args, c->lvars, sl_vector_at (c->space, i), false,
		      (nbc > 0) ? true : false);
      fflush (fout);
    }

  SL_DEBUG ("\t nbc=%zu\n", nbc);
  assert (nbc > 0);

  return 1;
}

int
sl_pred_2slide (FILE * fout, sl_pred_t * p)
{

  assert (NULL != fout);
  assert (NULL != p);

  SL_DEBUG ("Defs %s ...\n", p->pname);

  fprintf (fout, "\n%s(", p->pname);
  for (size_t i = 1; i < sl_vector_size (p->def->args); i++)
    {
      if (i > 1)
	fprintf (fout, ",");
      fprintf (fout, "%s", sl_var_2slide (NULL, p->def->args, i));
    }
  fprintf (fout, ") ::=  ");

  // Print all rules
  for (size_t i = 0; i < sl_vector_size (p->def->cases); i++)
    {
      // print separator
      if (i > 0)
	fprintf (fout, " |\n  ");

      // print rule
      if (!sl_pred_case_2slide (fout, p->def->args,
				sl_vector_at (p->def->cases, i)))
	return 0;
    }

  fprintf (fout, "\n");
  return 1;
}


/* ====================================================================== */
/* Problem */
/* ====================================================================== */
void
sl_prob_2slide (const char *fname)
{

  assert (NULL != fname);
  assert (sl_prob != NULL);

  sl_message ("*** Translation to Slide");

  /* Output filename */
  char *fname_out = (char *) malloc (strlen (fname) + 10);
  snprintf (fname_out, strlen (fname) + 10, "%s.sld", fname);

  /* Output file */
  sl_message ("\tOutput file: ");
  sl_message (fname_out);
  FILE *fout = fopen (fname_out, "w");
  if (!fout)
    {
      printf ("Can not create file '%s'!\nquit.", fname_out);
      return;
    }

  fprintf (fout, "RootCall ");

  // translate positive formula
  if (!sl_form_2slide (fout, sl_prob->pform))
    {
      sl_error (1, "sl_prob_2slide", "input formula in incorect form");
      goto endslide;
    }

  // Translate the problem only for sat
  if (!sl_vector_empty (sl_prob->nform))
    {
      //fprintf (fout, " |- ");
      // translate negative formula
      // sl_form_2slide (fout, sl_vector_at (sl_prob->nform, 0));
      sl_warning ("sl_prob_2slide", "entailment problem NYI");
    }
  // Translate predicates
  size_t last = sl_vector_size (preds_array) - 1;
  for (size_t i = 0; i <= last; i++)
    {
      if (!sl_pred_2slide (fout, sl_vector_at (preds_array, i)))
	{
	  sl_error (1, "sl_prob_2slide", "NYI predicat definition");
	  goto endslide;
	}
    }

endslide:
  fflush (fout);
  fclose (fout);

  sl_message ("\nDone\n");
}
