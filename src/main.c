#include <stdio.h>

#include "cli/parameters.h"

#include "server/server.h"

#include "pervasive.h"

static void print_help ()
{
	printf
	(
		"Zero of One - server version %d - protocol version %d\n"
		"\nUsages:\n"
		"   SERVER:\tzero_of_one_server SESSION_NAME MARKOV_ORDER STORAGE_FILE\n"
		"   CLEAN UP:\tzero_of_one_server -c SESSION_NAME\n"
		"   SHOW HELP:\tAnything else\n"
		"\nParameters:\n"
		"   SESSION_NAME: valid POSIX message queue filename.\n"
		"   MARKOV_ORDER: non-null positive integer.\n"
		"   STORAGE_FILE: file in which the knowledge will be stored.",
      ZoO_SERVER_VERSION,
      ZoO_PROTOCOL_VERSION
	);
}

int main (int const argc, const char * argv [const static argc])
{
   struct ZoO_parameters params;

   switch (ZoO_parameters_initialize(&params, argc, argv))
   {
      case ZoO_CLEANS_UP:
         return ZoO_server_cleanup_session(params.session);

      case ZoO_RUNS:
         return ZoO_server_main(params);

      default:
      case ZoO_PRINTS_HELP:
         print_help();
         return 0;
   }
}
