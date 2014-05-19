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

#ifndef _SL_TYPE_H_
#define _SL_TYPE_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "sl_vector.h"
#include "sl_util.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Identifiers type */
  typedef uid_t uid_t;

/** Constant used to signal an undefined identifier */
#define UNDEFINED_ID UINT32_MAX

/** Vector of identifiers */
    SL_VECTOR_DECLARE (sl_uid_array, uid_t);

/** Vector of integers */
    SL_VECTOR_DECLARE (sl_uint_array, uint_t);

/** Basic types used in SL */
  typedef enum
  {
    SL_TYP_BOOL = 0,
    SL_TYP_FIELD,
    SL_TYP_INT,
    SL_TYP_RECORD,
    SL_TYP_SETLOC,
    SL_TYP_SETREF,
    SL_TYP_SPACE,
    SL_TYP_OTHER
  } sl_typ_t;

/** Type expression.
 */
  typedef struct sl_type_t
  {
    sl_typ_t kind;
    sl_uid_array *args;		// type arguments, including the record index
  } sl_type_t;

/** Record information:
 * - the name of the record declared in the program
 * - the list of reference fields
 */
  typedef struct sl_record_t
  {
    char *name;			// declaration name
    uid_t rid;			// record identifier, 0 for void*
    sl_uid_array *flds;		// fields of this record
  } sl_record_t;

#define SL_TYP_VOID 0

/** Type of the global array of records. */
    SL_VECTOR_DECLARE (sl_record_array, sl_record_t *);

/** Kind of fields wrt their use in predicate definitions.
 */
  typedef enum
  {
    SL_PFLD_NONE = 0,
    SL_PFLD_BCKBONE,		/* F^0 */
    SL_PFLD_INNER,		/* F^1 */
    SL_PFLD_NULL,		/* F^2 needed? */
    SL_PFLD_BORDER,		/* F^2 */
    SL_PFLD_NESTED
  } sl_field_e;

/** Field information:
 * - the name of the field declared in the program
 * - the source record
 * - the target record
 */
  typedef struct sl_field_t
  {
    char *name;			// declaration name
    uid_t fid;			// field identifier
    uid_t src_r;		// identifier of the source record
    uid_t pto_r;		// identifier of the target record
    uid_t order;		// order number wrt use in predicates
    uid_t pid;			// predicate where the fields is used in the matrix
    sl_field_e kind;		// kind of the field wrt predicate pid
  } sl_field_t;


/** Type of the global array of fields.
 */
    SL_VECTOR_DECLARE (sl_field_array, sl_field_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

  extern sl_record_array *records_array;
  extern sl_field_array *fields_array;

/* Initialize global arrays of records and fields */
  void sl_record_init (void);
  void sl_field_init (void);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

  sl_record_t *sl_record_new (const char *name, sl_uid_array * flds);
  sl_type_t *sl_record_register (const char *name);
/* Declares a record and put it in the global array.
 * Returns the entry in the global array.
 */
  sl_type_t *sl_record_find (const char *name);


  sl_field_t *sl_field_new (const char *name, uid_t ty_src, uid_t ty_dst);
// uid_t sl_field_array_add (const char* name, uid_t ty_src, uid_t ty_dst);
  sl_type_t *sl_field_register (const char *name, sl_type_t * t);
/* Declared a filed and put it in the global array. */
  uid_t sl_field_array_find (const char *name);
/* Returns the id of the field with the given name. */

  sl_type_t *sl_mk_type_bool (void);
  sl_type_t *sl_mk_type_int (void);
  sl_type_t *sl_mk_type_field (uid_t src, uid_t dest);
  sl_type_t *sl_mk_type_record (uid_t rid);
  sl_type_t *sl_mk_type_setloc (void);
  sl_type_t *sl_mk_type_setref (uid_t ty);
  sl_type_t *sl_mk_type_space (void);
/* Constructors for the predefined types. */
  sl_type_t *sl_type_clone (sl_type_t * a);
  void sl_type_free (sl_type_t * a);

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

  uid_t sl_is_record (uid_t rid);
/* Returns rid if the arguments is a valid record index, otherwise UNDEFINED_ID. */

// searching

// inserting

  char *sl_field_name (uid_t fid);
  char *sl_record_name (uid_t rid);
/* Accessors */

  bool sl_field_lt (uid_t lhs, uid_t rhs);
/* Ordering */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

  void sl_fields_array_fprint (FILE * f, const char *msg);
  void sl_records_array_fprint (FILE * f, const char *msg);
/* Print the global arrays. */

#ifdef __cplusplus
}
#endif

#endif				/* _SL_TYPE_H_ */
