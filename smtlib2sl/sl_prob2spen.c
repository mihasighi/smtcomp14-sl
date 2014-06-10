/**************************************************************************/
/*                                                                        */
/*  Compiler for SMTLIB2 format for Separation Logic                      */
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
 * Translation to the Spen format
 */

#include <sys/time.h>
#include <stdio.h>

#include "sl.h"
#include "sl_form.h"
#include "sl_prob.h"
#include "sl_prob2spen.h"

/* ====================================================================== */
/* Types and Fields */
/* ====================================================================== */

void 
sl_types_2spen(FILE* fout, sl_record_array* records_array) {
  assert (NULL != fout);
  assert (NULL != records_array);
  
  for (size_t i = 1; i < sl_vector_size(records_array); i++) {
    fprintf (fout, "(declare-sort %s 0)\n", sl_record_name(i));
  }
  fprintf (fout, "\n");
}

void 
sl_fields_2spen(FILE* fout, sl_field_array* fields_array) {
  assert (NULL != fout);
  assert (NULL != fields_array);
  
  for (size_t i = 0; i < sl_vector_size(fields_array); i++) {
    sl_field_t* f = sl_vector_at(fields_array,i);
    fprintf (fout, "(declare-fun %s () (Field %s %s))\n", 
      f->name, sl_record_name(f->src_r), sl_record_name(f->pto_r));
  }
  fprintf (fout, "\n");
}

/* ====================================================================== */
/* Vars */
/* ====================================================================== */

sl_var_t *
sl_getvar_2spen (sl_var_array * args, sl_var_array * lvars, uid_t vid)
{

  uid_t fstlocal = (args == NULL) ? 0 : sl_vector_size (args);
  if (vid >= fstlocal)
    return sl_vector_at(lvars, vid - fstlocal);
  else
    return sl_vector_at(args, vid);
}

char *
sl_var_2spen (sl_var_array * args, sl_var_array * lvars, uid_t vid)
{

  char *vname;
  uid_t fstlocal = (args == NULL) ? 0 : sl_vector_size (args);
  if (vid >= fstlocal)
    {
      vname = sl_var_name (lvars, vid - fstlocal, SL_TYP_RECORD);
    }
  else
    vname = sl_var_name (args, vid, SL_TYP_RECORD);
  return vname;
}


void
sl_var_array_2spen (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		       sl_uid_array * va)
{

  for (size_t i = 0; i < sl_vector_size (va); i++)
    {
      fprintf (fout, "%s ", sl_var_2spen (args, lvars,
					    sl_vector_at (va, i)));
    }
}

/* ====================================================================== */
/* Formula */
/* ====================================================================== */

void
sl_pure_2spen (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		  sl_pure_t * form)
{
  assert (NULL != form);

  // shall always start by the local vars
  char *vleft = sl_var_2spen (args, lvars, form->vleft);

  char *vright = sl_var_2spen (args, lvars, form->vright);

  fprintf (fout, "(%s %s %s) ", 
	   (form->op == SL_PURE_EQ) ? "=" : "distinct", 
	   vleft, vright);
}

int
sl_space_2spen (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		   sl_space_t * form, int idx)
{

  assert (NULL != form);

  int nbls = 0;
  
  switch (form->kind)
    {
    case SL_SPACE_PTO:
      {
	// print source
	fprintf (fout, "\n\t\t(pto %s ",
		 sl_var_2spen (args, lvars, form->m.pto.sid));
	// print destinations
	if (sl_vector_size (form->m.pto.dest) > 1)
	  fprintf (fout, "(sref ");
	for (size_t ri = 0; ri < sl_vector_size (form->m.pto.dest); ri++) {
	  uid_t fi = sl_vector_at (form->m.pto.fields, ri);
	  uid_t vi = sl_vector_at (form->m.pto.dest, ri);
	  fprintf (fout, "(ref %s %s) ", sl_field_name(fi),
	  sl_var_2spen(args, lvars, vi));
	  }
	if (sl_vector_size (form->m.pto.dest) > 1)
	  fprintf (fout, ") "); // end:sref
	  
	fprintf (fout, ") "); // end:pto
	break;
      }

    case SL_SPACE_LS:
      {
	fprintf (fout, "\n\t\t");
	// print index
	if (idx >= 0)
	  fprintf (fout, "(index alpha%d ", idx + nbls);
	// print predicate
	fprintf (fout, "(%s ", sl_pred_name (form->m.ls.pid));
	// print arguments
	sl_var_array_2spen (fout, args, lvars, form->m.ls.args);
	fprintf (fout, ")");
	if (idx >= 0)
	  fprintf (fout, ") ");
	nbls++;
	break;
      }

    default:
      {
	sl_error (1, "sl_space_2spen:", "spatial formula not LS or PTO");
      }
    }
    return nbls;
}

int
sl_form_2spen (FILE * fout, sl_form_t * form, int idx)
{
  assert (NULL != fout);
  assert (NULL != form);

  size_t nbc = 0;
  int nbls = 0;

  // expected type: boolean
  
  // print 'and', if needed
  if (form->pure != NULL && 
      (sl_vector_size(form->pure) >= 1)) // ||
       // (sl_vector_size (form->pure) == 1 && form->space != NULL)
      //))
    fprintf (fout, "\n\t(and ");
  
  // start with pure formula
  for (size_t i = 0; i < sl_vector_size (form->pure); i++)
    {
      sl_pure_2spen (fout, NULL, form->lvars,
			sl_vector_at (form->pure, i));
      fflush (fout);
      nbc++;
    }

  if (form->space != NULL) {
  // continue with spatial formulas
  fprintf (fout, "\n\t(tobool ");
  nbc++;
  // Only ssep atomic formulas
  switch (form->space->kind)
    {
    case SL_SPACE_LS:  {
	nbls += sl_space_2spen (fout, NULL, form->lvars, form->space, idx + nbls);
	break;
    }
    case SL_SPACE_PTO:
      {
	sl_space_2spen (fout, NULL, form->lvars, form->space, idx+nbls);
	break;
      }
    case SL_SPACE_SSEP:
      {
	if (sl_vector_size (form->space->m.sep) > 1)
	      fprintf (fout, "\n\t(ssep ");
	for (size_t i = 0; i < sl_vector_size (form->space->m.sep); i++)
	  {
	    nbls += sl_space_2spen (fout, NULL, form->lvars,
			       sl_vector_at (form->space->m.sep, i), idx + nbls);
	    fflush (fout);
	  }
	if (sl_vector_size (form->space->m.sep) > 1)
	      fprintf (fout, "\n\t)\n"); // end:ssep
	break;
      }
    default:
      {
	sl_error (1, "sl_form_2spen:", "not a PTO, LS, SSEP formula");
	return nbls;
      }
    }
  fprintf (fout, "\n\t)\n"); // end:tobool
  }
  else  {
  fprintf (fout, "\n\t(tobool emp)\n"); 
  nbc++;
}
  
  if (nbc > 1)
  fprintf (fout, "\n\t)\n"); // end:and
  
  return nbls;
}

/* ====================================================================== */
/* Predicate */
/* ====================================================================== */
void
sl_pred_case_2spen (FILE * fout, sl_var_array * args, sl_pred_case_t * c)
{
  assert (NULL != fout);
  assert (NULL != args);
  assert (NULL != c);

  // is of boolean type!
  // print existentials, if any
  if (c->lvars != NULL && !sl_vector_empty (c->lvars))
    {
      fprintf (fout, "\n\t(exists (");
      for (size_t i = 0; i < sl_vector_size (c->lvars); i++)
	{
	  sl_var_t* v = sl_vector_at(c->lvars, i);
	  fprintf (fout, "(%s %s) ", v->vname,
	  sl_record_name (sl_vector_at(v->vty->args,0)));
	}
      fprintf (fout, ") ");
    }

  // start with pure formula
  if (sl_vector_size (c->pure) > 0)
    fprintf (fout, "\n\t(and ");
  for (size_t i = 0; i < sl_vector_size (c->pure); i++)
    {
      sl_pure_2spen (fout, args, c->lvars, sl_vector_at (c->pure, i));
    }

  // continue with spatial formulas
  fprintf (fout, "\n\t\t(tobool %s", 
    (sl_vector_size(c->space) > 0) ? "(ssep " : "");
  size_t nbs = 0;
  for (size_t i = 0; i < sl_vector_size (c->space); i++)
    {
      sl_space_2spen (fout, args, c->lvars, sl_vector_at (c->space, i), -1);
      fflush (fout);
      nbs++;
    }
 
  if (nbs == 0) {
    // maybe emp or junk
    if (c->is_precise)
       fprintf (fout, "emp");
    else
       fprintf (fout, "true");
    nbs++;
  }
  fprintf (fout, "\n\t\t)%s\n",
    (sl_vector_size(c->space)> 0) ? " )" : ""); // end:tobool,ssep

  SL_DEBUG ("\t nbs=%zu\n", nbs);
  assert (nbs > 0);
  
  if (sl_vector_size (c->pure) > 0)
    fprintf (fout, "\n\t)\n "); // end:and
  if (c->lvars != NULL && !sl_vector_empty (c->lvars))
    fprintf (fout, "\n\t)\n"); // end:exists
    
}

void
sl_pred_2spen (FILE * fout, sl_pred_t * p)
{

  assert (NULL != fout);
  assert (NULL != p);

  fprintf (fout, "\n(define-fun %s (", p->pname);
      for (size_t vi = 1; vi <= p->def->argc; vi++)
	{
	  sl_var_t* v = sl_vector_at (p->def->args, vi);
	  fprintf (fout, "(%s %s) ", v->vname,
	  sl_record_name (sl_vector_at(v->vty->args,0)));
	}
      fprintf (fout, ")");
  fprintf (fout, " Space (tospace \n");
  
  SL_DEBUG ("Defs %s ...\n", p->pname);

  assert (NULL != p->def);

  // Print all cases
  if (sl_vector_size(p->def->cases) > 1)
     fprintf (fout, "\t(or "); 
  for (size_t i = 0; i < sl_vector_size (p->def->cases); i++)
    {
      // print formula
      sl_pred_case_2spen (fout, p->def->args,
			     sl_vector_at (p->def->cases, i));
    }
  if (sl_vector_size(p->def->cases) > 1)
     fprintf (fout, "\n\t)"); // end:or
  fprintf (fout, "\n))\n"); // end:tospace,define-fun
}


/* ====================================================================== */
/* Problem */
/* ====================================================================== */
void
sl_prob_2spen (const char *fname)
{

  assert (NULL != fname);
  assert (sl_prob != NULL);

  sl_message ("*** Translation to Spen");

  /* Output filename */
  char *fname_out = (char *) malloc (strlen (fname) + 10);
  snprintf (fname_out, strlen (fname) + 10, "%s.spn", fname);

  /* Output file */
  sl_message ("\tOutput file: ");
  sl_message (fname_out);

  // first part put in a preliminaries file
  FILE *fdef = fopen ("file_decl", "w");
  if (!fdef)
    {
      printf ("Can not create declaration file!\nquit.");
      return;
    }
  // Translates logic
  fprintf (fdef, "\n(set-logic QF_S)\n");
  
  // Translates sorts
  fprintf (fdef, "\n;; declare sorts\n");
  sl_types_2spen(fdef, records_array);
  
  // Translates fields
  fprintf (fdef, "\n;; declare fields\n");
  sl_fields_2spen(fdef, fields_array);
  
  // Translates predicates
  fprintf (fdef, "\n;; declare predicates\n");
  for (size_t i = 0; i < sl_vector_size (preds_array); i++)
    {
      sl_pred_2spen (fdef, sl_vector_at (preds_array, i));
    }

  // Translate global vars
  fprintf (fdef, "\n;; declare variables\n");
  for (size_t vi = 1; vi < sl_vector_size(sl_prob->pform->lvars); vi++) {
	  sl_var_t* v = sl_vector_at (sl_prob->pform->lvars, vi);
	  if (v->scope == SL_SCOPE_GLOBAL)
	    fprintf (fdef, "(declare-fun %s () %s)\n", v->vname,
		sl_record_name (sl_vector_at(v->vty->args,0)));
	  else
	    break;
  }

  // Translated the problem and register SetLoc variables
  FILE *fprob = fopen ("file_prob", "w");
  if (!fprob)
    {
      printf ("Can not create file '%s'!\nquit.", fname_out);
      return;
    }

  int nbalpha = 0;
  
  // translate positive formula
      if (sl_prob->pform != NULL) {
      fprintf (fprob, "\n(assert ");
      nbalpha += sl_form_2spen (fprob, sl_prob->pform, 0);
      fprintf (fprob, "\n)\n"); // end:assert
  }

  // translate negative formula
      if (sl_prob->nform != NULL && !sl_vector_empty(sl_prob->nform)) {
      fprintf (fprob, "\n(assert (not ");
      nbalpha += sl_form_2spen (fprob, sl_vector_at (sl_prob->nform, 0), nbalpha);
      fprintf (fprob, "\n))\n"); // end:assert, not
  }
      
  // print command
      fprintf (fprob, "\n(check-sat)\n"); 
  
  
  fclose (fprob);

  // declare SetLoc variables
  fprintf (fdef, "\n;; declare set of locations\n");
  for (int i = 0; i < nbalpha; i++)
    fprintf (fdef, "\n(declare-fun alpha%d () SetLoc)", i);
  fprintf (fdef, "\n");
  fclose (fdef);
  
  // concat declaration files with problem file
  char *command = malloc (200 * sizeof (char));
  sprintf (command, "cat file_decl file_prob > %s", fname_out);

  if (system (command) == -1)
    {
      printf ("Error writing the file %s!\nquit.", fname_out);
    }

  
  sl_message ("\nDone\n");
}
