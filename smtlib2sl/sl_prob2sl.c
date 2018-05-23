/**************************************************************************/
/*                                                                        */
/*  Compiler for SMTLIB2 format for Separation Logic                       */
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
 * Translation to the new format for SL
 */

#include <sys/time.h>
#include <stdio.h>

#include "sl.h"
#include "sl_form.h"
#include "sl_prob.h"
#include "sl_prob2sl.h"

/* ====================================================================== */
/* References */
/* ====================================================================== */
void
sl_reference_2sl(FILE* fout, sl_record_array* arr)
{
  assert (NULL != fout);
  assert (NULL != arr);

  // Each record shall have a reference sort of name 'Ref'.record-name
  fprintf (fout, "; Sorts for locations, one by cell sort\n");
  for (size_t i = 1; i < sl_vector_size (arr); i++)
    {
      sl_record_t * r = sl_vector_at (arr, i);
      fprintf (fout, "(declare-sort Ref%s 0)\n", r->name);
    }
  // If no record defined, declare a generic reference sort
  if (sl_vector_size (arr) == 1)
    {
      fprintf (fout, "(declare-sort Ref 0)\n");
    }
}

/* ====================================================================== */
/* Records */
/* ====================================================================== */

void
sl_record_2sl (FILE * fout, sl_record_array * arr)
{
  assert (NULL != fout);
  assert (NULL != arr);

  fprintf (fout, "\n; Types of cells in the heap\n");

  // Special case of no recrod defined
  if (sl_vector_size (arr) == 1) {
    fprintf (fout, "\n; Cell are of Int type\n");
    return;
  }
  
  fprintf (fout, "\n(declare-datatypes (\n");
  // Declare names
  for (size_t i = 1; i < sl_vector_size (arr); i++) {
    sl_record_t* r = sl_vector_at (records_array, i);
    fprintf (fout, "\t(%s 0)\n", r->name);
  }
  fprintf (fout, "\t) (\n");
  // Declare constructors -- one by record
  // the record names are replaced by references to records
  for (size_t i = 1; i < sl_vector_size (arr); i++) {
    sl_record_t* r = sl_vector_at (records_array, i);
    fprintf (fout, "\t((c_%s ", r->name);
    // fields
    for (uint_t i = 0; i < sl_vector_size (r->flds); i++)
    {
      uid_t fi = sl_vector_at (r->flds, i);
      sl_field_t *fldi = sl_vector_at (fields_array, fi);
      fprintf (fout, "(%s ", fldi->name);
      char* rn = sl_record_name (fldi->pto_r);
      if (strcmp(rn, "Int") != 0 || strcmp(rn, "Bool") != 0)
	fprintf (fout, "Ref");
      fprintf (fout, "%s) ", rn);
    }
    // constructor end
    fprintf (fout, "))\n");
  }
  // end of datatypes
  fprintf (fout, "\t)\n)\n");

}

size_t heap_rid = UNDEFINED_ID;

void
sl_heap_2sl(FILE * fout, sl_record_array* arr)
{

  fprintf (fout, "\n; Type of heap\n");
  fprintf (fout, "\n(declare-heap ");
  for (size_t i = 1; i < sl_vector_size (arr); i++)
    {
      sl_record_t* r = sl_vector_at (records_array, i);
      fprintf (fout, "(Ref%s %s) ", r->name, r->name);
      heap_rid = i;
    }
  // If no record defined, declare a generic reference sort
  if (sl_vector_size (arr) == 1)
    {
      fprintf (fout, "(Ref Int) ");
    }
  fprintf (fout, "\n)\n");
}

/* ====================================================================== */
/* Vars */
/* ====================================================================== */

void
sl_var_2sl (FILE* fout, sl_var_array * args, sl_var_array * lvars, uid_t vid,
	    bool inpred, uid_t rctx)
{
  char *vname;
  
  char * rname = (rctx == SL_TYP_VOID) ? "" : sl_record_name(rctx);
  if (vid == VNIL_ID && inpred == inpred)
    {
      fprintf (fout, "(as nil Ref%s)", rname);
      return;
    }

  uid_t fstlocal = (args == NULL) ? 0 : sl_vector_size (args);
  // printf("fstlocal = %d, vid = %d\n", fstlocal, vid);
  if (vid >= fstlocal)
    vname = sl_var_name (lvars, vid - fstlocal, SL_TYP_RECORD);
  else 
    vname = sl_var_name (args, vid, SL_TYP_RECORD);
  if (vname[0] == '?')
    fprintf (fout, "%s", vname + 1); 
  else if (strcmp(vname,"nil") == 0) {
   fprintf (fout, "(as nil Ref%s)", rname);
  } else
    fprintf (fout, "%s", vname);
  // return (vname[0] == '?') ? vname + 1 : vname;
}

uid_t
sl_vartype_2sl (sl_var_array * args, sl_var_array * lvars, uid_t vid,
               bool inpred)
{
  /*
  if (inpred && vid == 1) {
    return sl_var_record(args, vid);
  } 
  */

  if (vid == VNIL_ID)
    return (heap_rid == UNDEFINED_ID) ? SL_TYP_VOID : heap_rid; // TODO : type
  
  uid_t fstlocal = (args == NULL) ? 0 : sl_vector_size (args);
  uid_t lstlocal = sl_vector_size(lvars) + fstlocal;
  if (vid < fstlocal && inpred)
    // arguments   
    return sl_var_record (args, vid);

  if (vid >= fstlocal && vid < lstlocal)
    return sl_var_record (lvars, vid - fstlocal);
  else {
    // error
    sl_error (1, "sl_vartype_2sl:", "unknown type for variable");
    return SL_TYP_VOID;
  }
}

void
sl_var_array_2sl (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		  sl_uid_array * va, uint_t start, bool inpred)
{

  size_t va_sz = sl_vector_size (va);
  // uid_t rid = sl_vartype_2sl(args, lvars, start, inpred);
  for (uint_t i = start; i < va_sz; i++)
    {
      uid_t vid = sl_vector_at (va, i);
      uid_t rid = (i < sl_vector_size(args) && inpred) ? sl_var_record(args, i) : 
	          sl_vartype_2sl(args, lvars, vid, inpred);
      // TODO: sl_vartype_2sl(args, lvars, vid, vidx, inpred);
      sl_var_2sl (fout, args, lvars, vid, inpred, rid);
      fprintf (fout, " ");
    }
}

/* ====================================================================== */
/* Formula */
/* ====================================================================== */

void
sl_pure_2sl (FILE * fout, sl_var_array * args, sl_var_array * lvars,
	     sl_pure_t * form, bool inpred)
{
  assert (NULL != form);

  uid_t rleft = sl_vartype_2sl(args, lvars, form->vleft, inpred);
  uid_t rright = sl_vartype_2sl(args, lvars, form->vright, inpred);
  uid_t rid = rright;
  if (rleft != rright) {
    sl_error (1, "sl_pure_2sl:", "pure terms of different type");
  }
  if (rid == UNDEFINED_ID || rid == SL_TYP_VOID) 
    rid = heap_rid;
  
  // shall always start by the local vars
  fprintf (fout, "(%s ", (form->op == SL_PURE_EQ) ? "=" : "distinct");
  sl_var_2sl (fout, args, lvars, form->vleft, inpred, rid); // rright
  fprintf (fout, " ");
  sl_var_2sl (fout, args, lvars, form->vright, inpred, rid); // rleft
  fprintf (fout, ")");

}

void
sl_space_2sl (FILE * fout, sl_var_array * args, sl_var_array * lvars,
		 sl_space_t * form, bool inpred)
{

  assert (NULL != form);

  // Only pto and predicates are allowed, all precise
  switch (form->kind)
    {
    case SL_SPACE_PTO:
      {
	// print source
	sl_var_array *src_vars = (args == NULL
				  || (form->m.pto.sid >
				      sl_vector_size (args))) ? lvars : args;
	fprintf (fout, "(pto ");
	uid_t rid = sl_vartype_2sl (args, lvars, form->m.pto.sid, inpred);
	rid = (rid == SL_TYP_VOID) ? heap_rid : rid; // src NEVER NIL
	sl_var_2sl (fout, args, lvars, form->m.pto.sid, inpred, rid); 
	fprintf (fout, " ");
	// print destination
	if (rid != SL_TYP_VOID && rid != 0) {
	  sl_record_t* r = sl_vector_at (records_array, rid);
	  // the type of the variable is a record
	  fprintf (fout, "(c_%s ", r->name);
	  // print destinations with the order given by the record declaration
	  for (uint_t j = 0; j < sl_vector_size (r->flds); j++)
	    {
	      uid_t fi = sl_vector_at (r->flds, j);
	      uid_t fi_rid = sl_vector_at (fields_array, fi)->pto_r;
	      // search destination
	      int isin = 0;
	      for (size_t i = 0; i < sl_vector_size (form->m.pto.dest); i++)
		{
		  uid_t fi_pto = sl_vector_at (form->m.pto.fields, i);
		  if (fi == fi_pto) {
		    uid_t vi = sl_vector_at (form->m.pto.dest, i);
		    sl_var_2sl (fout, args, lvars, vi, inpred, fi_rid);
		    fprintf (fout, " ");
		    isin = 1;
		  }
		}
	      if (!isin)
		{
		  sl_var_2sl (fout, args, lvars, VNIL_ID, inpred, fi_rid);
		  fprintf (fout, " ");
		}
	    }
	  fprintf (fout, "))");
	}
	else {
	  // the type of the variable is Int
	  sl_var_2sl (fout, args, lvars, sl_vector_at (form->m.pto.dest, 0), inpred, 0);
	  fprintf (fout, " )"); 
	}
	break;
      }

    case SL_SPACE_LS:
      {
	// print first argument and predicate
	fprintf (fout, "(%s ", sl_pred_name (form->m.ls.pid));
        // printf("predicate name %s\n", sl_pred_name (form->m.ls.pid));
        sl_var_array* fargs = sl_pred_getpred(form->m.ls.pid)->def->args;
        for (uint_t i = 1; i < sl_vector_size(fargs); i++) { // +1 for nil
            uid_t rid = sl_var_record(fargs, i); 
            // printf("\ttype arg %d : %s\n", i, sl_record_name(rid));
            sl_var_2sl (fout, args, lvars, 
                        sl_vector_at (form->m.ls.args, i-1), // -1 for nil
                        inpred, rid);
            fprintf (fout, " "); 
        }
        /*
        uid_t rid = sl_var_record(args, 0);
	//sl_vartype_2sl(args, lvars, sl_vector_at (form->m.ls.args, 0), inpred);
	rid = (rid == SL_TYP_VOID) ? heap_rid : rid;
	sl_var_2sl (fout, args, lvars, sl_vector_at (form->m.ls.args, 0),
		    inpred, rid); 
	fprintf (fout, " "); 
	// print remainder arguments
	sl_var_array_2sl (fout, args, lvars, form->m.ls.args, 1, inpred); */
	fprintf (fout, ")");
	break;
      }

    default:
      {
	sl_error (1, "sl_space_2sl:", "spatial formula not LS or PTO");
      }
    }
}

size_t
sl_form_pure_2sl(FILE * fout, sl_var_array * args, sl_var_array * lvars, 
		 sl_pure_array * form, bool inpred)
{
  size_t nbc = 0;
  size_t nb_pure = (form == NULL) ? 0 : sl_vector_size (form);
  if (nb_pure > 0) {
    fprintf (fout, "\n\t\t(and ");
    for (size_t i = 0; i < nb_pure; i++)
      {
        fprintf (fout, "\n\t\t\t");
        sl_pure_2sl (fout, args, lvars, sl_vector_at (form, i), inpred);
        fflush (fout);
        nbc++;
      }
  }
  return nbc;
}

size_t
sl_form_space_2sl(FILE * fout, sl_var_array * args, sl_var_array * lvars, 
		  sl_space_t ** form, uint_t size, bool inpred)
{
  size_t nbc = 0;
  // fprintf(fout, "space formula form %p of size %d\n", form, size);

  if (form == NULL) {
    // require the type of the heap to type 'emp'
    uint_t rid = UNDEFINED_ID;
    if (lvars != NULL && !sl_vector_empty (lvars)) {
       rid = sl_vartype_2sl(args, lvars, 1, inpred); 
    } else {
      // use the type of the heap
      rid = heap_rid;
    }
    if (rid == UNDEFINED_ID)
      fprintf (fout, "\n\t\t\t(_ emp Ref Int)"); // declared by default
    else {
      char * rname = sl_record_name(rid);
      fprintf (fout, "\n\t\t\t(_ emp Ref%s %s)", rname, rname);
    }

    return 1;
  }

  
  if (size > 1) {
    // only atoms are present
    fprintf (fout, "\n\t\t(sep ");
  }
  for (uint_t f = 0; f < size; f++) {
    sl_space_t * fi = *(form + f);
    // continue with spatial formulas
    switch (fi->kind)
    {
    case SL_SPACE_PTO:
    case SL_SPACE_LS:
      {
	fprintf (fout, "\n\t\t\t");
	sl_space_2sl (fout, args, lvars, fi, inpred);
	nbc++;
	break;
      }
    case SL_SPACE_SSEP:
      {
	if (size == 1 && sl_vector_size (fi->m.sep) > 1)
	  fprintf (fout, "\n\t\t(sep ");
	for (size_t i = 0; i < sl_vector_size (fi->m.sep); i++)
	  {
	    fprintf (fout, "\n\t\t\t");
	    sl_space_2sl (fout, args, lvars,
			  sl_vector_at (fi->m.sep, i), inpred);
	    fflush (fout);
	    nbc++;
	  }
	if (size == 1 && sl_vector_size (fi->m.sep) > 1)
	  fprintf (fout, "\n\t\t)\n");
	break;
      }
    default:
      {
	sl_error (1, "sl_form_space_2sl:", "not a PTO, LS, SSEP formula");
	break;
      }
    }
  }
  if (size > 1) {
    // end (sep
    fprintf (fout, "\n\t\t)\n");
  }
  return nbc;
}

void
sl_form_2sl (FILE * fout, sl_form_t * form)
{
  assert (NULL != fout);
  assert (NULL != form);

  size_t nbc = 0;
  
  // start with pure formulas, if any
  size_t nb_pure = sl_form_pure_2sl(fout, NULL, form->lvars, form->pure, false);
  
  // continue with space, if any
  size_t nb_space = 0;
  if (form->space == NULL) 
     nb_space = sl_form_space_2sl(fout, NULL, form->lvars, NULL, 0, false);
  else
     nb_space = sl_form_space_2sl(fout, NULL, form->lvars, &(form->space), 1, false);

  
  if (nb_pure == 0 && nb_space == 0) {
    fprintf (fout, " true");
    sl_error (1, "sl_form_2sl:", "empty formula");
    return;
  }

  if (nb_pure > 0) {
    // end (and 
    fprintf (fout, "\n\t\t)\n");
  }

}

/* ====================================================================== */
/* Predicate */
/* ====================================================================== */
void
sl_pred_case_2sl (FILE * fout, sl_var_array * args, sl_pred_case_t * c)
{
  assert (NULL != fout);
  assert (NULL != args);
  assert (NULL != c);

  // start with existentials
  if (c->lvars != NULL && !sl_vector_empty (c->lvars))
    {
      fprintf (fout, "(exists (");
      for (size_t i = 0; i < sl_vector_size (c->lvars); i++)
	{
	  fprintf (fout, "(");
	  uid_t rid = sl_vartype_2sl (args, c->lvars, c->argc + i + 1, true);
	  sl_var_2sl (fout, args, c->lvars, c->argc + i + 1, true, rid); 
	  fprintf (fout, " ");
	  if (sl_is_record(rid) == UNDEFINED_ID) 
		  fprintf (fout, "Int)");
	  else
		  fprintf (fout, "Ref%s)", sl_record_name(rid));
	}
      fprintf (fout, ")\n\t ");
    }
  
  // start with pure formulas, if any 
  size_t nb_pure = sl_form_pure_2sl(fout, args, c->lvars, c->pure, true);
  // continue with space part
  size_t nb_space = sl_form_space_2sl(fout, args, c->lvars, SL_VECTOR_ARRAY(c->space),
			   SL_VECTOR_SIZE(c->space), true);
    
  if (nb_pure > 0) {
    // end (and
    fprintf (fout, "\n\t\t)\n");
  }

  // end (exists
  if (c->lvars != NULL && !sl_vector_empty (c->lvars))
    fprintf (fout, "\n\t\t)\n");

  SL_DEBUG ("\t nbc=%zu\n", nb_pure+nb_space);

  assert (nbc > 0);
  
}

void
sl_pred_2sl (FILE * fout, sl_pred_t * p, int part)
{

  assert (NULL != fout);
  assert (NULL != p);

  SL_DEBUG ("Defs %s ...\n", p->pname);

  assert (NULL != p->def);

  if (part == 0) {
    // print predicate declaration/profile
    //fprintf (fout, "\n(define-fun-rec %s (", p->pname);
    fprintf (fout, "%s (", p->pname);
    for (size_t vi = 1; vi <= p->def->argc; vi++) {
      fprintf (fout, "(");
      uid_t rid = sl_vartype_2sl (NULL, p->def->args, vi, false);
      sl_var_2sl (fout, NULL, p->def->args, vi, false, rid);
      fprintf (fout, " ");
      if (sl_is_record(rid) == UNDEFINED_ID)
	fprintf (fout, "Int)");
      else
	fprintf (fout, "Ref%s)", sl_record_name(rid));
    }
    fprintf (fout, ") Bool\n\t");
    
  } else {

    size_t nb_cases = sl_vector_size (p->def->cases);
    if (nb_cases >= 2)
      fprintf (fout, "(or ");
    // Print all cases
    for (size_t i = 0; i < sl_vector_size (p->def->cases); i++)
      {
	// print separator
	if (i > 0)
	  fprintf (fout, "\n\t");
	// print formula using self for the first parameter
	sl_pred_case_2sl (fout, p->def->args,
			  sl_vector_at (p->def->cases, i));
      }

    // end (or and (define-fun-rec
    if (nb_cases >= 2)
      fprintf (fout, "\n\t)");
  }
  
}


/* ====================================================================== */
/* Problem */
/* ====================================================================== */
void
sl_prob_2sl (const char *fname)
{

  assert (NULL != fname);
  assert (sl_prob != NULL);

  sl_message ("*** Translation to smtlib-sl");

  /* Output filename */
  char *fname_out = (char *) malloc (strlen (fname) + 10);
  snprintf (fname_out, strlen (fname) + 10, "%s.sl2", fname);

  /* Output file */
  sl_message ("\tOutput file: ");
  sl_message (fname_out);
  FILE *fout = fopen (fname_out, "w");
  if (!fout)
    {
      printf ("Can not create file '%s'!\nquit.", fname_out);
      return;
    }

  // Logic: to be fixed by benchmark, not read
  // Infos: to be fixed by benchmark, not read

  // Define reference sorts, one by record
  sl_reference_2sl(fout, records_array);
  
  // Translates records, without void, using reference sorts and datatypes  
  sl_record_2sl(fout, records_array);

  // Declare heap type, only for typechecking of points-to and emp atoms
  sl_heap_2sl(fout, records_array);
  
  // Translates predicates
  size_t plen = sl_vector_size (preds_array);
  if (plen <= 0) {
    fprintf (fout, "; No user defined predicates\n\n");
  } else if (plen == 1) {
    fprintf (fout, "; User defined predicate\n");
    fprintf (fout, "(define-fun-rec ");
  } else {
    fprintf (fout, "; User defined predicates\n");
    fprintf (fout, "(define-funs-rec (");
  }
  for (size_t i = 0; i < plen; i++)
    {
      if (plen > 1) fprintf (fout, "\n\t(");
      sl_pred_2sl (fout, sl_vector_at (preds_array, i), 0); // dec
      if (plen > 1) fprintf (fout, ")\n");
    }
  if (plen > 1) fprintf (fout, "\t\t)\n\t\t(");
  for (size_t i = 0; i < plen; i++)
    {
      sl_pred_2sl (fout, sl_vector_at (preds_array, i), 1); // term
      fprintf (fout, "\n\t");
    }
  if (plen > 1)	fprintf (fout, "\t)\n)\n");
  else fprintf (fout, ")\n");
  

  // Translated the problem only for entailment
  fprintf (fout, "\n\n(check-unsat) ");

  // translate free variables
  fprintf (fout, "\n;; variables\n");
  for (size_t vi = 1; vi < sl_vector_size(sl_prob->pform->lvars); vi++) {
          sl_var_t* v = sl_vector_at (sl_prob->pform->lvars, vi);
          if (v->scope == SL_SCOPE_GLOBAL)
	    // TODO: all variables are references
            fprintf (fout, "(declare-const %s Ref%s)\n", v->vname,
                sl_record_name (sl_vector_at(v->vty->args,0)));
          else
            break;
  }

  
  // translate positive formula
  fprintf (fout, "\n(assert ");
  sl_form_2sl (fout, sl_prob->pform);
  fprintf (fout, "\n)\n");

  if (sl_vector_empty (sl_prob->nform))
    fprintf (fout, "\n(check-sat)\n");
  else {
    // translate negative formula
    fprintf (fout, "\n(assert (not ");
    sl_form_2sl (fout, sl_vector_at (sl_prob->nform, 0));
    fprintf (fout, "\n))\n");
    fprintf (fout, "\n(check-unsat)\n");
  }
  
  fclose (fout);
  sl_message ("\nDone\n");
}
