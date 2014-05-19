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

/** Utilities for SL compilation
 */

#ifndef _SL_UTIL_H_
#define _SL_UTIL_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include "sl_vector.h"

  void sl_message (const char *msg);
  void sl_warning (const char *fun, const char *msg);
  void sl_error (int level, const char *fun, const char *msg);
  void sl_error_id (int level, const char *fun, const char *msg);
  void sl_error_args (int level, const char *fun, uint_t size,
		      const char *msg);
  int time_difference (struct timeval *result, struct timeval *t2,
		       struct timeval *t1);

#ifndef NDEBUG

#define SL_DEBUG(...) \
        do { \
                        fprintf (stderr, __VA_ARGS__); \
        } while (0)

#else				/* #ifndef NDEBUG */

#define SL_DEBUG(...)		/* empty */

#endif				/* #ifndef NDEBUG */

#ifdef __cplusplus
}
#endif

#endif				/* _SL_UTIL_H */
