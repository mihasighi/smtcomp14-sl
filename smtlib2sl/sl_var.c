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
 * Variables for SL.
 */

#include "sl_var.h"
#include "sl_util.h"

SL_VECTOR_DEFINE (sl_var_array, sl_var_t *);

/* ====================================================================== */
/* Constructors/destructors */

/* ====================================================================== */

sl_var_t *
sl_var_new (const char *name, sl_type_t * ty, sl_scope_e s)
{
  sl_var_t *v = (sl_var_t *) malloc (sizeof (sl_var_t));
  v->vname = strdup (name);
  v->vty = ty;
  v->scope = s;
  return v;
}

void
sl_var_free (sl_var_t * a)
{
  if (!a)
    return;
  if (a->vname)
    free (a->vname);
  if (a->vty)
    sl_type_free (a->vty);
  free (a);
}

sl_var_t *
sl_var_copy (sl_var_t * a)
{
  assert (a != NULL);
  sl_var_t *r = (sl_var_t *) malloc (sizeof (sl_var_t));
  r->vid = a->vid;
  r->vname = strdup (a->vname);
  r->vty = sl_type_clone (a->vty);
  r->scope = a->scope;
  return r;
}

sl_var_array *
sl_var_array_make (uid_t sz)
{
  sl_var_array *a = sl_var_array_new ();
  if (sz > 0)
    sl_var_array_reserve (a, sz);
  return a;
}

void
sl_var_register (sl_var_array * a, const char *name, sl_type_t * ty,
		 sl_scope_e scope)
{
  assert (ty && (ty->kind == SL_TYP_RECORD || ty->kind == SL_TYP_SETLOC));

  sl_var_t *v = sl_var_new (name, ty, scope);
  v->scope = scope;
  sl_var_array_push (a, v);
  v->vid = sl_vector_size (a) - 1;
  return;
}

uid_t
sl_var_array_find_local (sl_var_array * a, const char *name)
{
  if (a && (sl_vector_size (a) > 0))
    {
      uid_t sz = sl_vector_size (a);
      for (uid_t i = 0; i < sz; i++)
	if (sl_vector_at (a, i) && !strcmp (name, sl_vector_at (a, i)->vname))
	  return i;
    }
  return UNDEFINED_ID;
}

/** Used to obtain the name of a variable from an identifier.
 * @param a   local environment, if NULL search in global environment
 * @param vid variable identifier
 */
char *
sl_var_name (sl_var_array * a, uid_t vid, sl_typ_t ty)
{
  if (&ty != &ty)
    {
      assert (0);		// just to avoid an "unused parameter warning"
    }

  if (a == NULL)
    return "unknown";
  if (vid == VNIL_ID)
    {
      return "nil";
    }
  if (vid >= sl_vector_size (a))
    {
      printf
	("sl_var_name: called with identifier %d not in the local environment.\n",
	 vid);
      return "unknown";
    }
  return (sl_vector_at (a, vid))->vname;
}

uid_t
sl_var_record (sl_var_array * a, uid_t vid)
{
  assert (a);

  if (vid == VNIL_ID)
    return SL_TYP_VOID;
  if (vid != VNIL_ID && vid >= sl_vector_size (a))
    {
      if (vid >= sl_vector_capacity (a))
	{
	  sl_warning ("sl_var_record", "look outside vector capacity");
	  return UNDEFINED_ID;
	}
      sl_warning ("sl_var_record", "look outside vector size");
    }
  sl_var_t *v = sl_vector_at (a, vid);
  sl_type_t *ty = v->vty;
  if ((ty == NULL) || (ty->kind != SL_TYP_RECORD) || (ty->args == NULL))
    {
      fprintf (stdout, "Incorrect type for location variable %d.\n", vid);
      return UNDEFINED_ID;
    }
#ifndef NDEBUG
  //fprintf (stdout, "sl_var_record: var %s, tid = %d\n", v->vname, ty->kind);
  //fflush(stdout);
#endif
  uid_t tid = sl_vector_at (ty->args, 0);
  if ((tid >= sl_vector_size (records_array))
      || (sl_vector_at (records_array, tid) == NULL))
    {
      fprintf (stdout, "Unknown record type for location variable %d.\n",
	       vid);
      return UNDEFINED_ID;
    }
  return tid;
}

void
sl_var_array_fprint (FILE * f, sl_var_array * a, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  fflush (f);
  if (!a)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uid_t length_a = sl_vector_size (a);
  for (uid_t i = 0; i < length_a; i++)
    {
      sl_var_t *vi = sl_vector_at (a, i);
      assert (vi != NULL);
      sl_type_t *ti = vi->vty;
      if (vi->scope == SL_SCOPE_LOCAL)
	fprintf (f, "?");
      else
	fprintf (f, " ");

      if (ti->kind == SL_TYP_RECORD)
	{
	  uid_t rid = sl_vector_at (vi->vty->args, 0);
	  fprintf (f, "%s:%s, ", vi->vname, sl_record_name (rid));
	}
      else
	fprintf (f, "%s:SetLoc, ", vi->vname);
    }
  fprintf (f, " - ]");
  fflush (f);
}
