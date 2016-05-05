#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <signal.h>

#include "../tool/strings.h"

#include "../io/error.h"
#include "../io/parameters.h"
#include "../io/data_input.h"
#include "../io/network.h"


#include "knowledge.h"

#include "state_types.h"

static int run = 1;

static void request_termination (int const signo)
{
   if ((signo == SIGINT) || (signo == SIGTERM))
   {
      run = 0;
   }
}

static int initialize
(
   struct ZoO_state s [const static 1],
   int const argc,
   const char * argv [const static argc]
)
{
   ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One is initializing...");

   srand(time(NULL));

   /* prevents s [restrict] */
   if (ZoO_knowledge_initialize(&(s->knowledge)) < 0)
   {
      return -1;
   }

   if (ZoO_parameters_initialize(&(s->param), argc, argv) < 0)
   {
      ZoO_knowledge_finalize(&(s->knowledge));

      return -1;
   }

   return 0;
}

static int load_data_file (struct ZoO_state s [const static 1])
{
   struct ZoO_data_input input;
   char * result;

   if (ZoO_data_input_open(&input, s->param.data_filename) < 0)
   {
      return -1;
   }

   while
   (
      ZoO_data_input_read_line
      (
         &input,
         ZoO_knowledge_punctuation_chars_count,
         ZoO_knowledge_punctuation_chars
      ) == 0
   )
   {
      (void) ZoO_knowledge_assimilate
      (
         &(s->knowledge),
         &(input.string),
         s->param.aliases_count,
         s->param.aliases
      );
   }

   ZoO_data_input_close(&input);

   return 0;
}

static int finalize (struct ZoO_state s [const static 1])
{
   int error;

   ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One is finalizing...");

   error = 0;

   /* prevents s [restrict] */
   ZoO_knowledge_finalize(&(s->knowledge));

   return error;
}

static int network_connect (struct ZoO_state s [const static 1])
{
   return
      ZoO_network_connect
      (
         &(s->network),
         s->param.irc_server_addr,
         s->param.irc_server_port,
         s->param.irc_server_channel,
         s->param.irc_username,
         s->param.irc_realname,
         s->param.aliases[0]
      );
}

static int should_reply
(
   struct ZoO_parameters param [const restrict static 1],
   struct ZoO_strings string [const restrict static 1],
   int should_learn [const restrict static 1]
)
{
   ZoO_index i, j;

   for (i = 0; i < param->aliases_count; ++i)
   {
      if (ZoO_IS_PREFIX(param->aliases[i], string->words[0]))
      {
         *should_learn = 0;

         return 1;
      }

      for (j = 1; j < string->words_count; ++j)
      {
         if (ZoO_IS_PREFIX(param->aliases[i], string->words[j]))
         {
            *should_learn = 1;

            return 1;
         }
      }
   }

   *should_learn = 1;

   return (param->reply_rate >= (rand() % 100));
}

static void handle_message
(
   struct ZoO_state s [const static 1],
   struct ZoO_strings string [const restrict static 1],
   ssize_t const msg_offset,
   ssize_t const msg_size
)
{
   ZoO_char * line;
   int reply, learn;

   if
   (
      ZoO_strings_parse
      (
         string,
         (size_t) msg_size,
         (s->network.msg + msg_offset),
         ZoO_knowledge_punctuation_chars_count,
         ZoO_knowledge_punctuation_chars
      ) < 0
   )
   {
      ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Could not dissect msg.");

      return;
   }

   if (string->words_count == 0)
   {
      return;
   }

   reply = should_reply(&(s->param), string, &learn);

   if
   (
      reply
      &&
      (
         ZoO_knowledge_extend
         (
            &(s->knowledge),
            string,
            !learn,
            &line
         ) == 0
      )
   )
   {
      if (line[0] == ' ')
      {
         strcpy((s->network.msg), (line + 1));
      }
      else
      {
         strcpy((s->network.msg), line);
      }

      free((void *) line);

      ZoO_network_send(&(s->network));
   }

   if (learn)
   {
      (void) ZoO_knowledge_assimilate
      (
         &(s->knowledge),
         string,
         s->param.aliases_count,
         s->param.aliases
      );
   }
}

static int main_loop  (struct ZoO_state s [const static 1])
{
   struct ZoO_strings string;
   ssize_t msg_offset, msg_size;

   msg_offset = 0;
   msg_size = 0;

   ZoO_strings_initialize(&string);

   while (run)
   {
      if (ZoO_network_receive(&(s->network), &msg_offset, &msg_size) == 0)
      {
         handle_message(s, &string, msg_offset, msg_size);
      }
   }

   ZoO_strings_finalize(&string);

   ZoO_network_disconnect(&(s->network));

   return 0;
}

int main (int const argc, const char * argv [const static argc])
{
   struct ZoO_state s;

   if (initialize(&s, argc, argv) < 0)
   {
      return -1;
   }

   if (load_data_file(&s) < 0)
   {
      goto CRASH;
   }

   if (network_connect(&s) < 0)
   {
      goto CRASH;
   }

   if (main_loop(&s) < 0)
   {
      goto CRASH;
   }

   (void) finalize(&s);

   ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One terminated normally.");

   return 0;

   CRASH:
   {
      (void) finalize(&s);

      ZoO_S_DEBUG
      (
         ZoO_DEBUG_PROGRAM_FLOW,
         "Zero of One terminated by crashing."
      );

      return -1;
   }
}
