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

#ifndef _SL_VAR_H_
#define _SL_VAR_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdlib.h>
#include <limits.h>

#include "sl_type.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

#define VNIL_ID UNDEFINED_ID

/**
 * Visibility flag values
 */
  typedef enum
  {
    SL_SCOPE_LOCAL = 0, SL_SCOPE_GLOBAL, SL_SCOPE_OTHER
  } sl_scope_e;

/** Variable information for both locations and set of locations variables:
 * - the name of the variable in the program
 * - the type(s) of the variable
 * - flag for local or global
 */
  typedef struct sl_var_t
  {
    char *vname;		// declaration name
    uid_t vid;			// variable identifier
    sl_type_t *vty;		// type
    sl_scope_e scope;		// visibility
  } sl_var_t;

/** Type of the global array of variables. */
    SL_VECTOR_DECLARE (sl_var_array, sl_var_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

/*
 * Global variables are stored within the formulae,
 * in fields lvars and svars of sl_form_t.
 * They have the flag scope set to SL_SCOPE_GLOBAL.
 */

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */
  sl_var_t *sl_var_new (const char *name, sl_type_t * vty, sl_scope_e s);
/* Build a variable record. */
  void sl_var_free (sl_var_t * a);
/* Free a variable record. */
  sl_var_t *sl_var_copy (sl_var_t * a);
/* Makes a copy of the variable. */

  sl_var_array *sl_var_array_make (uint_t sz);
/* Allocate an array of size variables.
 The variables are initialized with NULL pointers. */

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

  void sl_var_register (sl_var_array * a, const char *name,
			sl_type_t * ty, sl_scope_e s);
/* Add a variable declaration to the array a. */

  uint_t sl_var_array_find_local (sl_var_array * a, const char *name);
/* Search the position of the variable name in the local array a. */

  char *sl_var_name (sl_var_array * a, uid_t vid, sl_typ_t ty);
  uint_t sl_var_record (sl_var_array * a, uid_t vid);
/* Accessors */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

  void sl_var_array_fprint (FILE * f, sl_var_array * a, const char *msg);
/* Print the array a. */

#ifdef __cplusplus
}
#endif

#endif				/* _SL_VAR_H_ */
