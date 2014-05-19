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

#ifndef _SL_FORM_H_
#define	_SL_FORM_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <stdio.h>
#include "sl_type.h"
#include "sl_var.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Pure atomic formulas.
 */
  typedef enum sl_pure_op_t
  {
    SL_PURE_EQ = 0, SL_PURE_NEQ, SL_PURE_OTHER
  } sl_pure_op_t;

  typedef struct sl_pure_t
  {
    /*  vleft op vright */
    sl_pure_op_t op;
    uid_t vleft;
    uid_t vright;
  } sl_pure_t;

    SL_VECTOR_DECLARE (sl_pure_array, sl_pure_t *);

/**
 * Spatial formulas.
 */

  typedef struct sl_space_s sl_space_t;	/* forward definition */
    SL_VECTOR_DECLARE (sl_space_array, sl_space_t *);

  typedef enum sl_space_op_t
  {
    SL_SPACE_EMP = 0,
    SL_SPACE_JUNK,
    SL_SPACE_PTO,
    SL_SPACE_LS,
    SL_SPACE_SSEP,
    SL_SPACE_OTHER
/* NOT TO BE USED */
  } sl_space_op_t;

/** Points-to constraint
 */
  typedef struct sl_pto_t
  {
    uid_t sid;			// source location
    sl_uid_array *fields;	// array of fields
    sl_uid_array *dest;		// array of destination locations
  } sl_pto_t;

/** List segment constraint
 */
  typedef struct sl_ls_t
  {
    uid_t pid;			// predicate
    sl_uid_array *args;		// arguments used
    bool is_loop;		// set if it is a loop instance
  } sl_ls_t;

  struct sl_space_s
  {
    sl_space_op_t kind;
    bool is_precise;

    union
    {
      sl_pto_t pto;		// points-to constraint
      sl_ls_t ls;		// list segment constraint
      sl_space_array *sep;	// 
    } m;
  };

/** Formula in SL */
  typedef struct sl_form_t
  {
    sl_var_array *lvars;	// local variables
    sl_pure_array *pure;	// pure part
    sl_space_t *space;		// space part
  } sl_form_t;

    SL_VECTOR_DECLARE (sl_form_array, sl_form_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

  sl_form_t *sl_form_new (void);
  sl_pure_t *sl_pure_new (void);
  sl_space_t *sl_space_new (void);
/* Allocation */

  void sl_form_free (sl_form_t * f);
  void sl_pure_free (sl_pure_t * p);
  void sl_space_free (sl_space_t * s);
/* Deallocation */

  void sl_pure_push (sl_pure_array * form, sl_pure_op_t op, uid_t v1,
		     uid_t v2);
/* Add equality/inequality pure formula */

/* ====================================================================== */
/* Typing */
/* ====================================================================== */

  int sl_form_type (sl_form_t * form);
  /* Type the formula */

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */


/* ====================================================================== */
/* Printing */
/* ====================================================================== */

  void sl_pure_array_fprint (FILE * f, sl_var_array * lvars,
			     sl_pure_array * phi);
  void sl_space_fprint (FILE * f, sl_var_array * lvars, sl_space_t * phi);
  void sl_form_fprint (FILE * f, sl_form_t * phi);

#ifdef	__cplusplus
}
#endif

#endif				/* _SL_FORM_H_ */
