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
 * Predicates for SL.
 */

#ifndef _SL_PRED_H_
#define	_SL_PRED_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include "sl_type.h"
#include "sl_var.h"
#include "sl_form.h"

  /* ====================================================================== */
  /* Datatypes */
  /* ====================================================================== */

  /** Predicate case 
   */
  typedef struct sl_pred_case_t
  {
    sl_var_array *lvars;	// existential variables for this case
    uint_t argc;		// after the argc parameters
    bool is_precise;		// default true

    sl_pure_array *pure;	// pure part
    sl_space_array *space;	// spatial part, including recursive call
  } sl_pred_case_t;

    SL_VECTOR_DECLARE (sl_pred_case_array, sl_pred_case_t *);

  /** Predicate definition
   */
  typedef struct sl_pred_binding_t
  {
    size_t pargs;		// type of list = number of arguments of this record type 2 or 4
    sl_var_array *args;		// nil + formal arguments 
    uint_t argc;		// number of formal arguments in the array above

    sl_pred_case_array *cases;	// definition part
  } sl_pred_binding_t;

  /** Predicate typing infos
   */
  typedef struct sl_pred_typing_t
  {
    /* typing record for this predicate, index in record_array
     */
    uid_t ptype0;
    /* array of size @global records_array 
     * with 1 for records covered by pred
     */
    sl_uint_array *ptypes;
    /* array of size @global fields_array 
     * with values of @type sl_pfld_t for each field used in pred
     */
    sl_uint_array *pfields;
    bool useNil;		/* the predicate use fields to nil */
    bool isTwoDir;		/* the predicate is a two direction */
    /* array of size @global preds_array
     * with values 1 for predicates called inside the definition of pred
     */
    sl_uint_array *ppreds;
  } sl_pred_typing_t;

  /** Predicate information:
   * - the name of the predicate
   * - the type(s) of the variable
   */
  typedef struct sl_pred_t
  {
    char *pname;		// declaration name
    uid_t pid;			// predicate identifier

    sl_pred_binding_t *def;	// predicate definition
    sl_pred_typing_t *typ;	// predicate typing infos
  } sl_pred_t;

  /** Type of the global array of predicates. */
    SL_VECTOR_DECLARE (sl_pred_array, sl_pred_t *);

  /* ====================================================================== */
  /* Globals */
  /* ====================================================================== */

  extern sl_pred_array *preds_array;	// predicates

  void sl_pred_init (void);
  /* Initialize global arrays of predicates */

  /* ====================================================================== */
  /* Predicate cases */
  /* ====================================================================== */

  sl_pred_case_t *sl_pred_case_new (uint_t argc);
  void sl_pred_case_array_add (sl_pred_case_array * pcases,
			       sl_pred_case_t * c);

  /* ====================================================================== */
  /* Other methods */
  /* ====================================================================== */

  uid_t sl_pred_array_find (const char *name);
  /* Returns the id of the predicate in preds_array */

  uid_t sl_pred_register (const char *pname, sl_pred_binding_t * def);
  /* Insert the predicate definition in the global array */

  uid_t sl_pred_typecheck_call (uid_t pid, uid_t * actuals_ty, uid_t size);
  /* Typecheck the call of name with the types of parameters given in
   * actuals_ty of length size.
   */

  const sl_pred_t *sl_pred_getpred (uid_t pid);
  /* Returns the predicate with given Predicate ID */

  const char *sl_pred_name (uid_t pid);
  /* Accessors */

  int sl_pred_type (void);
  /* Type the predicate definitions.
   */

  /* ====================================================================== */
  /* Printing */
  /* ====================================================================== */

  void sl_pred_array_fprint (FILE * f, sl_pred_array * a, const char *msg);
  /* Print the array a. */


#ifdef	__cplusplus
}
#endif

#endif				/* _SL_PRED_H_ */
