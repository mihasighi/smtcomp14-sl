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
 * Translation to the Sleek format
 */

#include <sys/time.h>
#include <stdio.h>

#include "sl.h"
#include "sl_form.h"
#include "sl_prob.h"
#include "sl_prob2sleek.h"


/* ====================================================================== */
/* Records */
/* ====================================================================== */

void
sl_record_2sleek (FILE * fout, sl_record_t * r)
{
  assert (NULL != fout);
  assert (NULL != r);

  fprintf (fout, "\ndata %s {", r->name);
  for (uint_t i = 0; i < sl_vector_size (r->flds); i++)
    {
      uid_t fi = sl_vector_at (r->flds, i);
      sl_field_t *fldi = sl_vector_at (fields_array, fi);
      fprintf (fout, "\n\t%s %s;", sl_record_name (fldi->pto_r), fldi->name);
    }
  fprintf (fout, "\n}.\n");
}

/* ====================================================================== */
/* Vars */
/* ====================================================================== */

char *
sl_var_2sleek (sl_var_array * args, sl_var_array * lvars, uid_t vid,
	       bool inpred)
{

  char *vname;
  if (inpred && vid == 1)
    return "self";

  if (vid == VNIL_ID)
    return "null";

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
sl_var_array_2sleek (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		     sl_uid_array * va, uint_t start, bool inpred)
{

  for (uint_t i = start; i < sl_vector_size (va); i++)
    {
      if (i > start)
	fprintf (fout, ",");
      fprintf (fout, "%s", sl_var_2sleek (args, lvars,
					  sl_vector_at (va, i), inpred));
    }
}

/* ====================================================================== */
/* Formula */
/* ====================================================================== */

void
sl_pure_2sleek (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		sl_pure_t * form, bool inpred)
{
  assert (NULL != form);

  // shall always start by the local vars
  char *vleft = sl_var_2sleek (args, lvars, form->vleft, inpred);

  char *vright = sl_var_2sleek (args, lvars, form->vright, inpred);

  fprintf (fout, "%s%s%s", vleft,
	   (form->op == SL_PURE_EQ) ? "=" : "!=", vright);
}

void
sl_space_2sleek (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		 sl_space_t * form, bool inpred)
{

  assert (NULL != form);

  // Only pto and ls are allowed, all precise
  switch (form->kind)
    {
    case SL_SPACE_PTO:
      {
	// print source
	sl_var_array *src_vars = (args == NULL
				  || (form->m.pto.sid >
				      sl_vector_size (args))) ? lvars : args;
	fprintf (fout, "%s::%s",
		 sl_var_2sleek (args, lvars, form->m.pto.sid, inpred),
		 sl_record_name (sl_var_record (src_vars, form->m.pto.sid)));
	// print destinations
	fprintf (fout, "<");
	for (size_t i = 0; i < sl_vector_size (form->m.pto.dest); i++)
	  {
	    uid_t fi = sl_vector_at (form->m.pto.fields, i);
	    uid_t vi = sl_vector_at (form->m.pto.dest, i);
	    fprintf (fout, "%s%s:%s", (i > 0) ? "," : "",
		     sl_field_name (fi),
		     sl_var_2sleek (args, lvars, vi, inpred));
	  }
	fprintf (fout, ">");
	break;
      }

    case SL_SPACE_LS:
      {
	// print first argument and predicate
	fprintf (fout, "%s::%s<",
		 sl_var_2sleek (args, lvars,
				sl_vector_at (form->m.ls.args, 0), inpred),
		 sl_pred_name (form->m.ls.pid));
	// print remainder arguments
	sl_var_array_2sleek (fout, args, lvars, form->m.ls.args, 1, inpred);
	fprintf (fout, ">");
	break;
      }

    default:
      {
	sl_error (1, "sl_space_2sleek:", "spatial formula not LS or PTO");
      }
    }
}

void
sl_form_2sleek (FILE * fout, sl_form_t * form)
{
  assert (NULL != fout);
  assert (NULL != form);

  size_t nbc = 0;

  // start with spatial formulas
  // Only ssep atomic formulas

  if (form->space != NULL)
    {

      switch (form->space->kind)
	{
	case SL_SPACE_PTO:
	case SL_SPACE_LS:
	  {

	    if (nbc > 0)
	      fprintf (fout, " * ");
	    sl_space_2sleek (fout, NULL, form->lvars, form->space, false);
	    nbc++;
	    break;
	  }
	case SL_SPACE_SSEP:
	  {
	    for (size_t i = 0; i < sl_vector_size (form->space->m.sep); i++)
	      {
		if (nbc > 0)
		  fprintf (fout, " * ");
		sl_space_2sleek (fout, NULL, form->lvars,
				 sl_vector_at (form->space->m.sep, i), false);
		fflush (fout);
		nbc++;
	      }
	    break;
	  }
	default:
	  {
	    sl_error (1, "sl_form_2sleek:", "not a PTO, LS, SSEP formula");
	    return;
	  }
	}
    }

  // start with spatial formula
  for (size_t i = 0; i < sl_vector_size (form->pure); i++)
    {
      if (nbc > 0)
	fprintf (fout, " & ");
      sl_pure_2sleek (fout, NULL, form->lvars, sl_vector_at (form->pure, i),
		      false);
      fflush (fout);
      nbc++;
    }


}

/* ====================================================================== */
/* Predicate */
/* ====================================================================== */
void
sl_pred_case_2sleek (FILE * fout, sl_var_array * args, sl_pred_case_t * c)
{
  assert (NULL != fout);
  assert (NULL != args);
  assert (NULL != c);

  size_t nbc = 0;

  fprintf (fout, "(");
  // start with existentials
  if (c->lvars != NULL && !sl_vector_empty (c->lvars))
    {
      fprintf (fout, "exists ");
      for (size_t i = 0; i < sl_vector_size (c->lvars); i++)
	{
	  if (i > 0)
	    fprintf (fout, ",");
	  fprintf (fout, "%s",
		   sl_var_2sleek (args, c->lvars, c->argc + i + 1, true));
	}
      fprintf (fout, ": ");
    }

  // start with spatial formulas
  for (size_t i = 0; i < sl_vector_size (c->space); i++)
    {
      if (nbc > 0)
	fprintf (fout, " * ");
      sl_space_2sleek (fout, args, c->lvars, sl_vector_at (c->space, i), true);	// in predicate
      fflush (fout);
      nbc++;
    }

  // continue with pure formula
  for (size_t i = 0; i < sl_vector_size (c->pure); i++)
    {
      if (nbc > 0)
	fprintf (fout, " & ");
      else {
	fprintf (fout, " emp & ");
	nbc++;
      }
      sl_pure_2sleek (fout, args, c->lvars, sl_vector_at (c->pure, i), true);	// in predicate
      fflush (fout);
      nbc++;
    }
    
  if (nbc == 0) {
    // maybe emp or junk
    if (c->is_precise)
       fprintf (fout, "emp");
    else
       fprintf (fout, "true");
    nbc++;
  }

  fprintf (fout, ")");

  SL_DEBUG ("\t nbc=%zu\n", nbc);

  assert (nbc > 0);

}

void
sl_pred_2sleek (FILE * fout, sl_pred_t * p)
{

  assert (NULL != fout);
  assert (NULL != p);

  SL_DEBUG ("Defs %s ...\n", p->pname);

  assert (NULL != p->def);
  
  // print predicate instance
  fprintf (fout, "\npred %s<", p->pname);
  for (size_t vi = 2; vi <= p->def->argc; vi++)
    {
      if (vi > 2)
	fprintf (fout, ",");
      fprintf (fout, "%s", sl_var_2sleek (NULL, p->def->args, vi, false));
    }
  fprintf (fout, "> ==  ");

  // Print all cases
  for (size_t i = 0; i < sl_vector_size (p->def->cases); i++)
    {
      // print separator
      if (i > 0)
	fprintf (fout, "\n\tor  ");
      // print formula using self for the first parameter
      sl_pred_case_2sleek (fout, p->def->args,
			   sl_vector_at (p->def->cases, i));
    }

  fprintf (fout, "\n.\n");
}


/* ====================================================================== */
/* Problem */
/* ====================================================================== */
void
sl_prob_2sleek (const char *fname)
{

  assert (NULL != fname);
  assert (sl_prob != NULL);

  sl_message ("*** Translation to sleek");

  /* Output filename */
  char *fname_out = (char *) malloc (strlen (fname) + 10);
  snprintf (fname_out, strlen (fname) + 10, "%s.sle", fname);

  /* Output file */
  sl_message ("\tOutput file: ");
  sl_message (fname_out);
  FILE *fout = fopen (fname_out, "w");
  if (!fout)
    {
      printf ("Can not create file '%s'!\nquit.", fname_out);
      return;
    }

  // Translates records, without void  
  for (size_t i = 1; i < sl_vector_size (records_array); i++)
    {
      sl_record_2sleek (fout, sl_vector_at (records_array, i));
    }

  // Translates predicates
  for (size_t i = 0; i < sl_vector_size (preds_array); i++)
    {
      sl_pred_2sleek (fout, sl_vector_at (preds_array, i));
    }

  // Translated the problem only for entailment
  fprintf (fout, "\n\ncheckentail ");

  // translate positive formula
  sl_form_2sleek (fout, sl_prob->pform);

  fprintf (fout, "\n\t |- ");

  if (sl_vector_empty (sl_prob->nform))
    fprintf (fout, "false\n");
  else
    // translate negative formula
    sl_form_2sleek (fout, sl_vector_at (sl_prob->nform, 0));

  fprintf (fout, ".\n");

  fclose (fout);
  sl_message ("\nDone\n");
}
