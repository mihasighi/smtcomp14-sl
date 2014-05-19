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
 * Abstract Syntax Tree of SL formulas.
 */

#include<sys/time.h>

#include "sl_form.h"
#include "sl_pred.h"

SL_VECTOR_DEFINE (sl_pure_array, sl_pure_t *);

SL_VECTOR_DEFINE (sl_space_array, sl_space_t *);

SL_VECTOR_DEFINE (sl_form_array, sl_form_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

sl_form_t *
sl_form_new ()
{
  sl_form_t *form = (sl_form_t *) malloc (sizeof (sl_form_t));
  form->lvars = sl_var_array_new ();
  form->pure = sl_pure_array_new ();
  form->space = sl_space_new ();
  return form;
}

void
sl_form_free (sl_form_t * form)
{
  assert (form != NULL);
  if (form->lvars != NULL)
    {
      sl_var_array_delete (form->lvars);
      form->lvars = NULL;
    }
  if (form->pure != NULL)
    {
      sl_pure_array_delete (form->pure);
      form->pure = NULL;
    }
  if (form->space != NULL)
    {
      sl_space_free (form->space);
      form->space = NULL;
    }
  free (form);
}

sl_pure_t *
sl_pure_new (void)
{
  sl_pure_t *ret = (sl_pure_t *) malloc (sizeof (struct sl_pure_t));
  ret->op = SL_PURE_EQ;
  ret->vleft = UNDEFINED_ID;
  ret->vright = UNDEFINED_ID;
  return ret;
}

void
sl_pure_free (sl_pure_t * p)
{
  if (!p)
    return;
  free (p);
}

sl_space_t *
sl_space_new ()
{
  sl_space_t *ret = (sl_space_t *) malloc (sizeof (sl_space_t));
  ret->kind = SL_SPACE_EMP;
  ret->is_precise = true;
  return ret;
}

void
sl_space_free (sl_space_t * s)
{
  if (!s)
    return;
  switch (s->kind)
    {
    case SL_SPACE_PTO:
      {
	if (sl_vector_size (s->m.pto.fields) > 0)
	  {
	    if (s->m.pto.fields)
	      sl_uid_array_delete (s->m.pto.fields);
	    if (s->m.pto.dest)
	      sl_uid_array_delete (s->m.pto.dest);
	  }
	break;
      }
    case SL_SPACE_LS:
      {
	if (s->m.ls.args && sl_vector_size (s->m.ls.args) > 0)
	  sl_uid_array_delete (s->m.ls.args);
	break;
      }
    case SL_SPACE_SSEP:
      {
	sl_space_array_delete (s->m.sep);
	break;
      }
    default:
      break;
    }
  free (s);
  return;
}

void
sl_pure_push (sl_pure_array * f, sl_pure_op_t op, uid_t v1, uid_t v2)
{
  assert (f != NULL);

  sl_pure_t *res = sl_pure_new ();
  res->op = op;
  res->vleft = (v1 <= v2) ? v1 : v2;	// lowest one for cyclist
  res->vright = (v1 <= v2) ? v2 : v1;
  sl_pure_array_push (f, res);
}

/* ====================================================================== */
/* Typing */
/* ====================================================================== */


/**
 * Type the formula @p form.
 * @return 0 if incorrect typing
 */
int
sl_form_type (sl_form_t * form)
{
  if (form != NULL)		// only to use form
    return 1;
  /* TODO: redo typing here */
  return 0;
}


/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void
sl_pure_array_fprint (FILE * f, sl_var_array * lvars, sl_pure_array * phi)
{
  if (!phi)
    {
      fprintf (f, "null\n");
      return;
    }
  for (size_t i = 0; i < sl_vector_size (phi); i++)
    {
      sl_pure_t *fi = sl_vector_at (phi, i);
      fprintf (f, "%s %s %s, ",
	       sl_var_name (lvars, fi->vleft, SL_TYP_RECORD),
	       (fi->op == SL_PURE_EQ) ? "=" : "<>",
	       sl_var_name (lvars, fi->vright, SL_TYP_RECORD));
    }
  fprintf (f, "\n");
}

void
sl_space_fprint (FILE * f, sl_var_array * lvars, sl_space_t * phi)
{
  if (!phi)
    {
      fprintf (f, "null\n");
      return;
    }

  if (phi->is_precise == true)
    fprintf (f, "[precise] ");
  else
    fprintf (f, "[junk] ");

  switch (phi->kind)
    {
    case SL_SPACE_EMP:
      fprintf (f, "emp");
      break;
    case SL_SPACE_JUNK:
      fprintf (f, "junk");
      break;
    case SL_SPACE_PTO:
      {
	fprintf (f, "(pto  ");
	if (lvars == NULL)
	  fprintf (f, "*%d ...)", phi->m.pto.sid);
	else
	  fprintf (f, "%s ...)", sl_vector_at (lvars, phi->m.pto.sid)->vname);
	break;
      }
    case SL_SPACE_LS:
      {
	const sl_pred_t *pred = sl_pred_getpred (phi->m.ls.pid);
	assert (NULL != pred);
	fprintf (f, "(%s", pred->pname);
	for (uid_t i = 0; i < sl_vector_size (phi->m.ls.args); i++)
	  {
	    uint_t vi = sl_vector_at (phi->m.ls.args, i);
	    if (lvars == NULL)
	      fprintf (f, " *%d ", vi);
	    else if (vi == VNIL_ID)
	      fprintf (f, " nil ");
	    else
	      fprintf (f, " %s ", sl_vector_at (lvars, vi)->vname);
	  }
	fprintf (f, ")");
	break;
      }
    default:
      {
	assert (phi->kind == SL_SPACE_SSEP);
	fprintf (f, "(ssep ");
	for (uid_t i = 0; i < sl_vector_size (phi->m.sep); i++)
	  {
	    sl_space_fprint (f, lvars, sl_vector_at (phi->m.sep, i));
	    fprintf (f, "\n\t");
	  }
	fprintf (f, ")");
	break;
      }
    }
}

void
sl_form_fprint (FILE * f, sl_form_t * phi)
{
  assert (f != NULL);

  if (!phi)
    {
      fprintf (stdout, "null\n");
      return;
    }

  fprintf (f, "\n\t lvars: ");
  sl_var_array_fprint (f, phi->lvars, "\t\t");
  fprintf (f, "\n\n\t pure part: \t");
  sl_pure_array_fprint (f, phi->lvars, phi->pure);
  fprintf (f, "\n\t spatial part: \t");
  sl_space_fprint (f, phi->lvars, phi->space);

}
