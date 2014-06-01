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
 * Defines the problem for the decision procedure.
 */

#ifndef SL_PROB_H_
#define SL_PROB_H_

#include <stdio.h>
#include "sl_form.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Problems encoded:
 *
 * Satisfiability problem
 *          phi     	sat
 *  encoded in the SMTLIB2 format
 *          (assert phi)
 *          (check-sat)
 *
 * Entailment problems
 *          phi ==> (\/_j psi_j)    valid
 *  read from the input file in the form
 *          phi /\ ! (\/_j psi_j)   unsat
 *  encoded in the SMTLIB2 format
 *          (assert phi)
 *          ;; for all j
 *          (assert (not psi_j))
 *          (check-sat)
 *
 */

typedef enum sl_prob_kind_t
{
  SL_PROB_UNSAT = 0, SL_PROB_SAT, NOLL_FORM_OTHER
/* NOT TO BE USED */
} sl_prob_kind_t;

typedef struct sl_prob_t
{
  char *smt_fname;		// smt file with entailment
  uid_t fst_pid;                // first predicate definition in file
  sl_form_t *pform;		// positive formula phi
  sl_form_array *nform;		// array of negative formulae psi
  sl_prob_kind_t cmd;		// command given: check-sat (default),
  //                check-unsat
} sl_prob_t;

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

extern sl_prob_t *sl_prob;	// problem of entailment in sl

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialization/Deallocation of formulas */
void sl_prob_init (void);
void sl_prob_free (void);

/* ====================================================================== */
/* Getters */
/* ====================================================================== */

sl_form_t *sl_prob_get_pform (void);
/* Get positive formula */
sl_form_t *sl_prob_get_nform_last (void);
/* Get last negative formulae */

/* ====================================================================== */
/* Setters */
/* ====================================================================== */

void sl_prob_set_fname (char *fname);
/* Set source file information */
void sl_prob_set_cmd (sl_prob_kind_t pb);
void sl_prob_set_pid (uid_t pid);

/* ====================================================================== */
/* Typechecking */
/* ====================================================================== */

int sl_prob_type (void);
/* Type the predicates, fields, formulas in sl_prob */

/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void sl_prob_fprint (FILE * f);


#endif /* SL_PROB_H_ */
