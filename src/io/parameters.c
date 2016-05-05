#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>

#include "../pervasive.h"

#include "error.h"

#include "parameters.h"

static void load_default_parameters
(
   struct ZoO_parameters param [const restrict static 1]
)
{
   param->data_filename       = ZoO_DEFAULT_DATA_FILENAME;

   param->irc_server_addr     = ZoO_DEFAULT_IRC_SERVER_ADDR;
   param->irc_server_port     = ZoO_DEFAULT_IRC_SERVER_PORT;
   param->irc_server_channel  = ZoO_DEFAULT_IRC_SERVER_CHANNEL;
   param->irc_username        = ZoO_DEFAULT_IRC_USERNAME;
   param->irc_realname        = ZoO_DEFAULT_IRC_REALNAME;

   param->reply_rate          = ZoO_DEFAULT_REPLY_RATE;

   param->aliases_count = 0;
   param->aliases = NULL;
}

static void print_help (const char exec [const restrict static 1])
{
   printf
   (
      "Usage: %s [option_1 option_2 ...] NICKNAME [ALIAS_1 ALIAS_2 ...] \n"
      "NICKNAME is used as the IRC nickname value.\n"
      "If NICKNAME or any ALIAS is found in an event, the program will reply.\n"
      "\nAvailable options:\n"
      "   [--data-filename | -df] FILENAME\n"
      "      Learn content from FILENAME before connecting.\n"
      "      Default: %s.\n"
      "   [--irc-server-addr | -isa] IRC_SERVER_ADDR\n"
      "      Connect to this server address.\n"
      "      Default: %s.\n"
      "   [--irc-server-port | -isp] IRC_SERVER_PORT\n"
      "      Connect to this server port.\n"
      "      Default: %s.\n"
      "   [--irc-server-channel | -isc] IRC_SERVER_CHANNEL\n"
      "      Connect to this server's channel.\n"
      "      Default: %s.\n"
      "   [--irc-username | -iu] USERNAME\n"
      "      Connect using this as 'username' (shown in WHOIS).\n"
      "      Default: %s.\n"
      "   [--irc-realname | -ir] REALNAME\n"
      "      Connect using this as 'realname' (shown in WHOIS).\n"
      "      Default: %s.\n"
      "   [--reply-rate | -rr] REPLY_RATE\n"
      "      Chance to reply to an event (integer, range [0, 100]).\n"
      "      Default: %d.\n",
      exec,
      ZoO_DEFAULT_DATA_FILENAME,
      ZoO_DEFAULT_IRC_SERVER_ADDR,
      ZoO_DEFAULT_IRC_SERVER_PORT,
      ZoO_DEFAULT_IRC_SERVER_CHANNEL,
      ZoO_DEFAULT_IRC_USERNAME,
      ZoO_DEFAULT_IRC_REALNAME,
      ZoO_DEFAULT_REPLY_RATE
   );
}

static int parse_string_arg
(
   const char * restrict dest [const restrict static 1],
   int const i,
   const char * restrict argv [const restrict static 1],
   int const argc
)
{
   if (i == argc)
   {
      ZoO_FATAL
      (
         "Missing value for parameter '%s'.",
         /* Safe: i > 1 */
         argv[i - 1]
      );

      return -1;
   }

   *dest = argv[i];

   return 0;
}

static int parse_integer_arg
(
   int dest [const restrict static 1],
   int const i,
   const char * argv [const restrict static 1],
   int const argc,
   int const min_val,
   int const max_val
)
{
   long int result;
   char * endptr;
   const int old_errno = errno;

   if (i == argc)
   {
      ZoO_FATAL
      (
         "Missing value for parameter '%s'.",
         /* Safe: i > 1 */
         argv[i - 1]
      );

      return -1;
   }

   errno = 0;

   result = strtol(argv[i], &endptr, 10);

   if
   (
      (errno != 0)
      || ((*endptr) == '\n')
      || (result < min_val)
      || (result > max_val)
   )
   {
      ZoO_FATAL
      (
         "Invalid or missing value for parameter '%s', accepted range is "
         "[%d, %d] (integer).",
         /* Safe: i > 1 */
         argv[i - 1],
         min_val,
         max_val
      );

      errno = old_errno;

      return -1;
   }

   *dest = (int) result;

   errno = old_errno;

   return 0;
}

int ZoO_parameters_initialize
(
   struct ZoO_parameters param [const restrict static 1],
   int const argc,
   const char * argv [const restrict static argc]
)
{
   int i;

   load_default_parameters(param);

   for (i = 1; i < argc; ++i)
   {
      if
      (
         (strcmp(argv[i], "--data-filename") == 0)
         || (strcmp(argv[i], "-df") == 0)
      )
      {
         i += 1;

         if
         (
            parse_string_arg
            (
               &(param->data_filename),
               i,
               argv,
               argc
            ) < 0
         )
         {
            return -1;
         }
      }
      else if
      (
         (strcmp(argv[i], "--irc-server-addr") == 0)
         || (strcmp(argv[i], "-isa") == 0)
      )
      {
         i += 1;

         if
         (
            parse_string_arg
            (
               &(param->irc_server_addr),
               i,
               argv,
               argc
            ) < 0
         )
         {
            return -1;
         }
      }
      else if
      (
         (strcmp(argv[i], "--irc-server-port") == 0)
         || (strcmp(argv[i], "-isp") == 0)
      )
      {
         i += 1;

         if
         (
            parse_string_arg
            (
               &(param->irc_server_port),
               i,
               argv,
               argc
            ) < 0
         )
         {
            return -1;
         }
      }
      else if
      (
         (strcmp(argv[i], "--irc-server-channel") == 0)
         || (strcmp(argv[i], "-isc") == 0)
      )
      {
         i += 1;

         if
         (
            parse_string_arg
            (
               &(param->irc_server_channel),
               i,
               argv,
               argc
            ) < 0
         )
         {
            return -1;
         }
      }
      else if
      (
         (strcmp(argv[i], "--irc-username") == 0)
         || (strcmp(argv[i], "-iu") == 0)
      )
      {
         i += 1;

         if
         (
            parse_string_arg
            (
               &(param->irc_username),
               i,
               argv,
               argc
            ) < 0
         )
         {
            return -1;
         }
      }
      else if
      (
         (strcmp(argv[i], "--irc-realname") == 0)
         || (strcmp(argv[i], "-in") == 0)
      )
      {
         i += 1;

         if
         (
            parse_string_arg
            (
               &(param->irc_realname),
               i,
               argv,
               argc
            ) < 0
         )
         {
            return -1;
         }
      }
      else if
      (
         (strcmp(argv[i], "--reply-rate") == 0)
         || (strcmp(argv[i], "-rr") == 0)
      )
      {
         i += 1;

         if
         (
            parse_integer_arg
            (
               &(param->reply_rate),
               i,
               argv,
               argc,
               0,
               100
            ) < 0
         )
         {
            return -1;
         }
      }
      else if
      (
         (strcmp(argv[i], "--help") == 0)
         || (strcmp(argv[i], "-h") == 0)
      )
      {
         print_help(argv[0]);

         return 0;
      }
      else
      {
         break;
      }
   }

   if (i == argc)
   {
      ZoO_S_FATAL("Missing argument: NICKNAME");

      print_help(argv[0]);

      return -1;
   }

   param->aliases_count = (argc - i);
   param->aliases = (argv + i);

   return 1;
}
