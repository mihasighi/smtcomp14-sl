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

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
#include "sl_util.h"

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

int sl_error_parsing = 0;

/*
 * ======================================================================
 * Messages
 * ======================================================================
 */

void
sl_message (const char *msg)
{
  fprintf (stdout, "smtlib2sl: %s\n", msg);
}

void
sl_warning (const char *fun, const char *msg)
{
  fprintf (stderr, "Warning in %s: %s.\n", fun, msg);
}

void
sl_error (int level, const char *fun, const char *msg)
{
  fprintf (stderr, "Error of level %d in %s: %s.\n", level, fun, msg);
  if (level == 0)
    //terminate
    exit (0);
  else
    sl_error_parsing = level;
}

void
sl_error_args (int level, const char *fun, uint_t size, const char *expect)
{
  fprintf (stderr,
	   "Error of level %d in %s: bad number (%d) of arguments, expected (%s).\n",
	   level, fun, size, expect);
  if (level == 0)
    //terminate
    exit (0);
  else
    sl_error_parsing = level;
}

void
sl_error_id (int level, const char *fun, const char *name)
{
  fprintf (stderr,
	   "Error of level %d in %s: identifier '%s' is not declared.\n",
	   level, fun, name);
  if (level == 0)
    //terminate
    exit (0);
  else
    sl_error_parsing = level;
}

/**
 *  * compute the difference between two times.
 *   *
 *    * @return 1 if the difference is negative, otherwise 0.
 *     */
int
time_difference (struct timeval *result, struct timeval *t2,
		 struct timeval *t1)
{
  long int diff = (t2->tv_usec + 1000000 * t2->tv_sec)
    - (t1->tv_usec + 1000000 * t1->tv_sec);
  result->tv_sec = diff / 1000000;
  result->tv_usec = diff % 1000000;

  return (int) (diff < 0);
}
