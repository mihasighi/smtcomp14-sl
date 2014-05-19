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
 * Type system for SL.
 */

#include "sl_type.h"

SL_VECTOR_DEFINE (sl_uid_array, uid_t);

SL_VECTOR_DEFINE (sl_uint_array, uint_t);

SL_VECTOR_DEFINE (sl_record_array, sl_record_t *);

SL_VECTOR_DEFINE (sl_field_array, sl_field_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

sl_record_array *records_array;
sl_field_array *fields_array;

/* Initialize global arrays of records and fields */
void
sl_record_init ()
{
  records_array = sl_record_array_new ();
  sl_record_array_reserve (records_array, 4);

  /* initialize with void* */
  sl_record_register ("void");
}

void
sl_field_init ()
{
  fields_array = sl_field_array_new ();
  sl_field_array_reserve (fields_array, 4);
}

/* ====================================================================== */
/* Constructors/destructors */

/* ====================================================================== */

sl_record_t *
sl_record_new (const char *name, sl_uid_array * flds)
{
  sl_record_t *r = (sl_record_t *) malloc (sizeof (sl_record_t));
  r->name = strdup (name);
  if (flds != NULL)
    r->flds = flds;
  else
    r->flds = sl_uid_array_new ();
  // there shall be one cell to store the record identifier
  if (sl_vector_size (r->flds) < 1)
    sl_uid_array_reserve (r->flds, 1);
  return r;
}

/**
 * Register a record.
 * Warning: does not test that the name already exists !
 */
sl_type_t *
sl_record_register (const char *name)
{
  // type expression for the result
  sl_type_t *ty = sl_mk_type_record (UNDEFINED_ID);
  // build the record
  sl_record_t *r = sl_record_new (name, NULL);
  // add to the global array
  sl_record_array_push (records_array, r);
  r->rid = sl_vector_size (records_array) - 1;
  // the index of the added record is last element of the array
  sl_vector_at (ty->args, 0) = r->rid;
  return ty;
}

/**
 * Find a record using its name.
 * @return a type built with this record or NULL if not find
 */
sl_type_t *
sl_record_find (const char *name)
{
  sl_type_t *ty = NULL;
  for (uint_t i = 0; i < sl_vector_size (records_array); i++)
    {
      sl_record_t *r = sl_vector_at (records_array, i);
      if (strcmp (r->name, name) == 0)
	{
	  ty = sl_mk_type_record (UNDEFINED_ID);
	  sl_vector_at (ty->args, 0) = r->rid;
	}
    }
  return ty;
}

sl_field_t *
sl_field_new (const char *name, uid_t ty_src, uid_t ty_dst)
{
  sl_field_t *f = (sl_field_t *) malloc (sizeof (sl_field_t));
  f->name = strdup (name);
  f->pto_r = ty_dst;
  f->src_r = ty_src;
  return f;
}

sl_type_t *
sl_field_register (const char *name, sl_type_t * ty)
{
  // type expression for the result is ty
  // extract informations about the field
  uid_t src = UNDEFINED_ID;
  uid_t dst = UNDEFINED_ID;
  if (!ty || ty->kind != SL_TYP_FIELD || ty->args == NULL
      || (sl_vector_size (ty->args) != 2))
    {
      // TODO: make error message
      printf ("Field declaration `%s': typing error.\n", name);
      return NULL;
    }
  // set src and dest
  src = sl_is_record (sl_vector_at (ty->args, 0));
  dst = sl_is_record (sl_vector_at (ty->args, 1));
  // create the field
  sl_field_t *f = sl_field_new (name, src, dst);
  // push the field
  sl_field_array_push (fields_array, f);
  f->fid = sl_vector_size (fields_array) - 1;
  // register the field in the src set of fields
  sl_record_t *r_src = sl_vector_at (records_array, src);
  sl_uid_array_push (r_src->flds, f->fid);
  // set order/pid to max
  f->order = UNDEFINED_ID;
  f->pid = UNDEFINED_ID;

  return ty;
}

uid_t
sl_field_array_find (const char *name)
{
  uid_t sz = sl_vector_size (fields_array);
  for (uid_t i = 0; i < sz; i++)
    if (!strcmp (name, sl_field_name (i)))
      return i;
  return UNDEFINED_ID;
}

sl_type_t *
sl_mk_type_bool ()
{
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = SL_TYP_BOOL;
  ret->args = sl_uid_array_new ();
  return ret;
}

sl_type_t *
sl_mk_type_int ()
{
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = SL_TYP_INT;
  ret->args = sl_uid_array_new ();
  return ret;
}

sl_type_t *
sl_mk_type_field (uid_t src, uid_t dst)
{
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = SL_TYP_FIELD;
  ret->args = sl_uid_array_new ();
  sl_uid_array_reserve (ret->args, 1);
  sl_uid_array_push (ret->args, src);
  sl_uid_array_push (ret->args, dst);
  return ret;
}

sl_type_t *
sl_mk_type_record (uid_t rid)
{
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = SL_TYP_RECORD;
  ret->args = sl_uid_array_new ();
  sl_uid_array_reserve (ret->args, 1);
  sl_uid_array_push (ret->args, rid);
  return ret;
}

sl_type_t *
sl_mk_type_setloc ()
{
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = SL_TYP_SETLOC;
  ret->args = sl_uid_array_new ();
  return ret;
}

sl_type_t *
sl_mk_type_setref (uid_t ty)
{
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = SL_TYP_SETREF;
  ret->args = sl_uid_array_new ();
  sl_uid_array_reserve (ret->args, 1);
  sl_uid_array_push (ret->args, ty);
  return ret;
}

sl_type_t *
sl_mk_type_space ()
{
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = SL_TYP_SPACE;
  ret->args = sl_uid_array_new ();
  return ret;
}

sl_type_t *
sl_type_clone (sl_type_t * a)
{
  if (!a)
    return a;
  sl_type_t *ret = (sl_type_t *) malloc (sizeof (struct sl_type_t));
  ret->kind = a->kind;
  ret->args = sl_uid_array_new ();
  sl_uid_array_copy (ret->args, a->args);
  return ret;
}

void
sl_type_free (sl_type_t * a)
{
  if (!a)
    return;
  if (a->args)
    sl_uid_array_delete (a->args);
  free (a);
}

/* ====================================================================== */
/* Other methods */

/* ====================================================================== */

uid_t
sl_is_record (uid_t rid)
{
  return (rid < sl_vector_size (records_array)) ? rid : UNDEFINED_ID;
}

char *
sl_field_name (uid_t fid)
{
  if (fid >= sl_vector_size (fields_array))
    {
      printf
	("sl_field_name: called with identifier %d not in the global environment.\n",
	 fid);
      return "unknown";
    }
  return sl_vector_at (fields_array, fid)->name;
}

char *
sl_record_name (uid_t rid)
{
  if (rid >= sl_vector_size (records_array))
    {
      printf
	("sl_record_name: called with identifier %d not in the global environment.\n",
	 rid);
      return "unknown";
    }
  return sl_vector_at (records_array, rid)->name;
}

/**
 * Ordering using the ordering of predicates.
 */
bool
sl_field_lt (uid_t lhs, uid_t rhs)
{

  assert (lhs < sl_vector_size (fields_array));
  assert (rhs < sl_vector_size (fields_array));

  sl_field_t *fl = sl_vector_at (fields_array, lhs);
  sl_field_t *fr = sl_vector_at (fields_array, rhs);

  assert (fl->order != UNDEFINED_ID);
  assert (fr->order != UNDEFINED_ID);
  assert (fl->order != fr->order);

  return (fl->order < fr->order);
}


/* ====================================================================== */
/* Printing */
/* ====================================================================== */


void
sl_fields_array_fprint (FILE * f, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  if (!fields_array)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uint_t length = sl_vector_size (fields_array);
  for (uint_t i = 0; i < length; i++)
    {
      sl_field_t *fi = sl_vector_at (fields_array, i);
      fprintf (f, " %s:%s->%s,",
	       fi->name, sl_record_name (fi->src_r),
	       sl_record_name (fi->pto_r));
    }
  fprintf (f, " - ]");
}

void
sl_records_array_fprint (FILE * f, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  if (!records_array)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uint_t length = sl_vector_size (records_array);
  for (uint_t i = 0; i < length; i++)
    {
      sl_record_t *ri = sl_vector_at (records_array, i);
      fprintf (f, " %s (", sl_record_name (i));
      if (!ri->flds)
	{
	  fprintf (f, "null),");
	  continue;
	}
      uint_t length_fld = sl_vector_size (ri->flds);
      for (uint_t j = 0; j < length_fld; j++)
	{
	  fprintf (f, "%s;", sl_field_name (sl_vector_at (ri->flds, j)));
	}
      fprintf (f, "),");
    }
  fprintf (f, " - ]");
}
