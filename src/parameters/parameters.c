#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

#include "../core/index.h"

#include "parameters.h"

static int parse_markov_order
(
   struct ZoO_parameters param [const restrict static 1],
   const char argv [const restrict]
)
{
	long long int input;
	const int old_errno = errno;

	errno = 0;

   input = strtoll(argv, (char **) NULL, 10);

   if
   (
      (errno != 0)
		|| (input > (long long int) ZoO_INDEX_MAX)
		|| (input < 1)
   )
   {
		fprintf
      (
			stderr,
         "[F] Invalid or value for parameter 'MARKOV_ORDER', accepted"
			"range is "
         "[1, %lli] (integer).",
         (long long int) ZoO_INDEX_MAX
      );

      errno = old_errno;

      return -1;
   }

	param->markov_order = (ZoO_index) input;

   errno = old_errno;

   return 0;
}

enum ZoO_invocation_objective ZoO_parameters_initialize
(
   struct ZoO_parameters param [const restrict static 1],
   int const argc,
   const char * argv [const static argc]
)
{
   param->session = (const char *) NULL;
   param->markov_order = 1;
   param->storage = (const char *) NULL;

   switch (argc)
   {
      case 4:
         param->session = argv[1];
         param->storage = argv[3];

         if (parse_markov_order(param, argv[2]) < 0)
         {
            return ZoO_PRINTS_HELP;
         }
         else
         {
            return ZoO_RUNS;
         }

      case 3:
         param->session = argv[1];

			return ZoO_CLEANS_UP;

      default:
         return ZoO_PRINTS_HELP;
   }
}
