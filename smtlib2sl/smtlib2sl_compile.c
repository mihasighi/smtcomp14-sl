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
#include "smtlib2sl.h"
#include "sl_prob2cyclist.h"
#include "sl_prob2sleek.h"
#include "sl_prob2slide.h"
#include "sl_prob2slp.h"
#include "sl_prob2sl.h"
#include "sl_prob2spen.h"

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

typedef enum sl_format_t
{
  SL_FORMAT_SL = 0,
  SL_FORMAT_CYCLIST,
  SL_FORMAT_SLEEK,
  SL_FORMAT_SLIDE,
  SL_FORMAT_SLP,
  SL_FORMAT_SL2,
  SL_FORMAT_SPEN,
  SL_FORMAT_OTHER		/* NOT TO BE USED */
} sl_format_t;

/* set by options */
bool sl_compile[SL_FORMAT_OTHER] = { true, false, false, false, false, false, false };

/* ====================================================================== */
/* MAIN/Main/main */
/* ====================================================================== */

/**
 * Set options declared in different files
 */
void
sl_set_option (char *option)
{
  if (0 == strcmp (option, "-cyclist"))
    sl_compile[SL_FORMAT_CYCLIST] = true;
  else if (0 == strcmp (option, "-sleek"))
    sl_compile[SL_FORMAT_SLEEK] = true;
  else if (0 == strcmp (option, "-slide"))
    sl_compile[SL_FORMAT_SLIDE] = true;
  else if (0 == strcmp (option, "-slp"))
    sl_compile[SL_FORMAT_SLP] = true;
  else if (0 == strcmp (option, "-sl2"))
    sl_compile[SL_FORMAT_SL2] = true;
  else if (0 == strcmp (option, "-spen"))
    sl_compile[SL_FORMAT_SPEN] = true;
  else

    printf ("Unknown option: %s! ignore.\n", option);
}

/**
 * Print informations on usage.
 */
void
print_help (void)
{
  printf
    ("smtlib2sl_compile: compiling SMTLIB v2 format for Separation Logic\n");
  printf ("Usage: smtlib2sl_compile [-cyclist|-sleek|-slide|-slp|-sl] <file>\n");
  printf ("\t<file>: input file in the SMTLIB v2 format for QF_S\n");
}

/**
 * Entry of the compiler.
 */
int
main (int argc, char **argv)
{
  // Step 0: Check the arguments
  if (argc <= 1)
    {
      print_help ();
      return 1;
    }
  int arg_file = 1;
  if (argc >= 2)
    {
      arg_file = argc - 1;
      for (int i = 1; i < arg_file; i++)
	sl_set_option (argv[i]);
    }

  // Step 1: Parse the file and initialize the problem
  // pre: the file shall exists.
  sl_message ("Parse input file");
  FILE *f = fopen (argv[arg_file], "r");
  if (!f)
    {
      printf ("File %s not found!\nquit.", argv[arg_file]);
      return 1;
    }

  // initialize the problem
  sl_prob_init ();
  sl_prob_set_fname (argv[arg_file]);
  // call the parser
  smtlib2_sl_parser *sp = smtlib2_sl_parser_new ();
  smtlib2_abstract_parser_parse ((smtlib2_abstract_parser *) sp, f);

  // Step 2: call the typing while seeing (check-sat)
  // done in (sl.c) sl_check
  // also sets the smtlib2 parser result

  // Step 3: compile to other formats
  for (size_t i = 1; i < SL_FORMAT_OTHER; i++)
    if (sl_compile[i])
      switch (i)
	{
	case SL_FORMAT_CYCLIST:
	  sl_prob_2cyclist (argv[arg_file]);
	  break;
	case SL_FORMAT_SLEEK:
	  sl_prob_2sleek (argv[arg_file]);
	  break;
	case SL_FORMAT_SLIDE:
	  sl_prob_2slide (argv[arg_file]);
	  break;
	case SL_FORMAT_SLP:
	  sl_prob_2slp (argv[arg_file]);
	  break;
	case SL_FORMAT_SL2:
	  sl_prob_2sl (argv[arg_file]);
	  break;
	case SL_FORMAT_SPEN:
	  sl_prob_2spen (argv[arg_file]);
	  break;
	default:
	  break;
	}

  // Step 4: finish (free memory, etc.)
  smtlib2_sl_parser_delete (sp);
  fclose (f);
  sl_prob_free ();

  return 0;
}
