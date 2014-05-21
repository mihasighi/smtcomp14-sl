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

/* Translation to Slide format
 */

#ifndef _SL_PROB2SLD_H_
#define _SL_PROB2SLD_H_

#ifdef __cplusplus
extern "C"
{
#endif

  void sl_prob_2slide (const char *fname);
  /* Translates into file fname.sld */

#ifdef __cplusplus
}
#endif

#endif				/* _SL_PROB2SLD_H_ */
