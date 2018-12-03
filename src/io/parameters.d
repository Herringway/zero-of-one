module io.parameters;

import core.stdc.string;
import core.stdc.stdio;
import core.stdc.stdlib;
import core.stdc.errno;

import io.parameters_types;
import io.error;

import pervasive;

void load_default_parameters
(
   ZoO_parameters* param
)
{
   param.data_filename        = ZoO_DEFAULT_DATA_FILENAME;
   param.new_data_filename    = null;

   param.irc_server_addr     = ZoO_DEFAULT_IRC_SERVER_ADDR;
   param.irc_server_port     = ZoO_DEFAULT_IRC_SERVER_PORT;
   param.irc_server_channel  = ZoO_DEFAULT_IRC_SERVER_CHANNEL;
   param.irc_username        = ZoO_DEFAULT_IRC_USERNAME;
   param.irc_realname        = ZoO_DEFAULT_IRC_REALNAME;

   param.reply_rate          = ZoO_DEFAULT_REPLY_RATE;

   param.aliases_count = 0;
   param.aliases = null;
}

void print_help (const char* exec)
{
   printf
   (
      "Usage: %s [option_1 option_2 ...] NICKNAME [ALIAS_1 ALIAS_2 ...] \n"~
      "NICKNAME is used as the IRC nickname value.\n"~
      "If NICKNAME or any ALIAS is found in an event, the program will reply.\n"~
      "\nAvailable options:\n"~
      "   [--data-filename | -df] FILENAME\n"~
      "      Learn content from FILENAME before connecting.\n"~
      "      Default: %s.\n"~
      "   [--new-data-filename | -ndf] FILENAME\n"~
      "      Store new data learned in FILENAME.\n"~
      "      Default: value of the --data-filename param.\n"~
      "   [--irc-server-addr | -isa] IRC_SERVER_ADDR\n"~
      "      Connect to this server address.\n"~
      "      Default: %s.\n"~
      "   [--irc-server-port | -isp] IRC_SERVER_PORT\n"~
      "      Connect to this server port.\n"~
      "      Default: %s.\n"~
      "   [--irc-server-channel | -isc] IRC_SERVER_CHANNEL\n"~
      "      Connect to this server's channel.\n"~
      "      Default: %s.\n"~
      "   [--irc-username | -iu] USERNAME\n"~
      "      Connect using this as 'username' (shown in WHOIS).\n"~
      "      Default: %s.\n"~
      "   [--irc-realname | -ir] REALNAME\n"~
      "      Connect using this as 'realname' (shown in WHOIS).\n"~
      "      Default: %s.\n"~
      "   [--reply-rate | -rr] REPLY_RATE\n"~
      "      Chance to reply to an event (integer, range [0, 100]).\n"~
      "      Default: %d.\n",
      exec,
      ZoO_DEFAULT_DATA_FILENAME.ptr,
      ZoO_DEFAULT_IRC_SERVER_ADDR.ptr,
      ZoO_DEFAULT_IRC_SERVER_PORT.ptr,
      ZoO_DEFAULT_IRC_SERVER_CHANNEL.ptr,
      ZoO_DEFAULT_IRC_USERNAME.ptr,
      ZoO_DEFAULT_IRC_REALNAME.ptr,
      ZoO_DEFAULT_REPLY_RATE
   );
}

int parse_string_arg
(
   const(char)** dest,
   const int i,
   const char** argv,
   const int argc
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


int parse_integer_arg
(
   int* dest,
   const int i,
   const char** argv,
   const int argc,
   const int min_val,
   const int max_val
)
{
   long result;
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

   result = strtol(cast(char*)argv[i], &endptr, 10);

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
         "Invalid or missing value for parameter '%s', accepted range is "~
         "[%d, %d] (integer).",
         /* Safe: i > 1 */
         argv[i - 1],
         min_val,
         max_val
      );

      errno = old_errno;

      return -1;
   }

   *dest = cast(int) result;

   errno = old_errno;

   return 0;
}

int ZoO_parameters_initialize
(
   ZoO_parameters* param,
   const int argc,
   const char** argv
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
               &(param.data_filename),
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
         (strcmp(argv[i], "--new-data-filename") == 0)
         || (strcmp(argv[i], "-ndf") == 0)
      )
      {
         i += 1;

         if
         (
            parse_string_arg
            (
               &(param.new_data_filename),
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
               &(param.irc_server_addr),
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
               &(param.irc_server_port),
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
               &(param.irc_server_channel),
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
               &(param.irc_username),
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
               &(param.irc_realname),
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
               &(param.reply_rate),
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

   param.aliases_count = (argc - i);
   param.aliases = &argv[i];

   if (param.new_data_filename == null)
   {
      param.new_data_filename = param.data_filename;
   }

   return 1;
}
