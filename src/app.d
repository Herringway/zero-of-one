module core.main;

import core.stdc.signal;
import core.stdc.stdlib;
import core.stdc.string;
import core.stdc.time;

import tool.strings;
import tool.strings_types;

import io.error;
import io.parameters;
import io.parameters_types;
import io.data_input;
import io.data_input_types;
import io.data_output;
import io.network;
import io.network_types;

import core.assimilate;
import core.create_sentences;
import core.knowledge;
import core.state_types;

import pervasive;

alias ssize_t = ptrdiff_t;

int run = 1;

void request_termination (const int signo)
{
   if ((signo == SIGINT) || (signo == SIGTERM))
   {
      run = 0;
   }
}

int initialize(ZoO_state* s, const int argc, const char** argv)
{
   ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One is initializing...");

   srand(cast(uint)time(null));

   /* prevents s [restrict] */
   if (ZoO_knowledge_initialize(&(s.knowledge)) < 0)
   {
      return -1;
   }

   if (ZoO_parameters_initialize(&(s.param), argc, argv) < 1)
   {
      ZoO_knowledge_finalize(&(s.knowledge));

      return -1;
   }

   return 0;
}

int load_data_file(ZoO_state* s)
{
   ZoO_data_input input;
   char* result;

   if (ZoO_data_input_open(&input, s.param.data_filename) < 0)
   {
      return -1;
   }

   while
   (
      ZoO_data_input_read_line
      (
         &input,
         ZoO_knowledge_punctuation_chars_count,
         ZoO_knowledge_punctuation_chars.ptr
      ) == 0
   )
   {
      cast(void) ZoO_knowledge_assimilate
      (
         &(s.knowledge),
         &(input.string),
         s.param.aliases_count,
         s.param.aliases
      );
   }

   ZoO_data_input_close(&input);

   return 0;
}


int finalize(ZoO_state* s)
{
   int error;

   ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One is finalizing...");

   error = 0;

   /* prevents s [restrict] */
   ZoO_knowledge_finalize(&(s.knowledge));

   return error;
}

int network_connect (ZoO_state* s)
{
   return
      ZoO_network_connect
      (
         &(s.network),
         s.param.irc_server_addr,
         s.param.irc_server_port,
         s.param.irc_server_channel,
         s.param.irc_username,
         s.param.irc_realname,
         s.param.aliases[0]
      );
}

int should_reply
(
   ZoO_parameters* param,
   ZoO_strings* string_,
   int* should_learn
)
{
   ZoO_index i, j;

   for (i = 0; i < param.aliases_count; ++i)
   {
      if (strncmp(param.aliases[i], string_.words[0], strlen(param.aliases[i])) == 0)
      {
         *should_learn = 0;

         return 1;
      }

      for (j = 1; j < string_.words_count; ++j)
      {
         if (strncmp(param.aliases[i], string_.words[j], strlen(param.aliases[i])) == 0)
         {
            *should_learn = 1;

            return 1;
         }
      }
   }

   *should_learn = 1;

   return (param.reply_rate >= (rand() % 100));
}

void handle_user_join
(
   ZoO_state* s,
   ZoO_strings* string_,
   const ssize_t msg_offset,
   const ssize_t msg_size
)
{
   ZoO_char* line;
   ZoO_index loc;

   if (s.param.reply_rate < (rand() % 100))
   {
      return;
   }

   if
   (
      ZoO_strings_parse
      (
         string_,
         cast(size_t) msg_size,
         (&s.network.in_[msg_offset]),
         cast(uint*)&ZoO_knowledge_punctuation_chars_count,
         cast(char*)&ZoO_knowledge_punctuation_chars
      ) < 0
   )
   {
      ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Could not dissect join username.");

      return;
   }

   if
   (
      (
      ZoO_knowledge_find
         (
            &(s.knowledge),
            string_.words[0],
            &loc
         ) < 0
      )
      || (s.knowledge.words[loc].backward_links_count <= 3)
      || (s.knowledge.words[loc].forward_links_count <= 3)
   )
   {
      if
      (
         ZoO_knowledge_extend
         (
            &(s.knowledge),
            cast(ZoO_strings *) null,
            0,
            cast(const char **) null,
            &line
         ) == 0
      )
      {
         if (line[0] == ' ')
         {
            strcpy((s.network.out_.ptr), (line + 1));
         }
         else
         {
            strcpy((s.network.out_.ptr), line);
         }

         free(cast(void *) line);

         ZoO_network_send(&(s.network));
      }
   }
   else
   {
      if
      (
         ZoO_knowledge_extend
         (
            &(s.knowledge),
            string_,
            0,
            cast(const char **) null,
            &line
         ) == 0
      )
      {
         if (line[0] == ' ')
         {
            strcpy((s.network.out_.ptr), (line + 1));
         }
         else
         {
            strcpy((s.network.out_.ptr), line);
         }

         free(cast(void *) line);

         ZoO_network_send(&(s.network));
      }
   }
}

void handle_message
(
   ZoO_state* s,
   ZoO_strings* string_,
   const ssize_t msg_offset,
   /* FIXME: somehow we end up using (msg_size + 1), meaning there's a mixup
    *        between size and length.
    */
   const ssize_t msg_size
)
{
   ZoO_char* line;
   int reply, learn;

   if
   (
      ZoO_strings_parse
      (
         string_,
         cast(size_t) msg_size,
         (&s.network.in_[msg_offset]),
         cast(uint*)&ZoO_knowledge_punctuation_chars_count,
         cast(char*)ZoO_knowledge_punctuation_chars.ptr
      ) < 0
   )
   {
      ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Could not dissect msg.");

      return;
   }

   if (string_.words_count == 0)
   {
      return;
   }

   reply = should_reply(&(s.param), string_, &learn);

   if (learn)
   {
      /*
       * It would be best to do that after replying, but by then we no longer
       * have the string in 's.network.in'.
       */
      cast(void) ZoO_data_output_write_line
      (
         s.param.new_data_filename,
         (&s.network.in_[msg_offset]),
         cast(size_t) (msg_size + 1)
      );
   }

   if
   (
      reply
      &&
      (
         ZoO_knowledge_extend
         (
            &(s.knowledge),
            string_,
            s.param.aliases_count,
            s.param.aliases,
            &line
         ) == 0
      )
   )
   {
      if (line[0] == ' ')
      {
         strcpy((s.network.out_.ptr), (line + 1));
      }
      else
      {
         strcpy((s.network.out_.ptr), line);
      }

      free(cast(void *) line);

      ZoO_network_send(&(s.network));
   }

   if (learn)
   {
      cast(void) ZoO_knowledge_assimilate
      (
         &(s.knowledge),
         string_,
         s.param.aliases_count,
         s.param.aliases
      );
   }
}

int main_loop(ZoO_state* s)
{
   ZoO_strings string_;
   ssize_t msg_offset, msg_size;
   ZoO_msg_type msg_type;

   msg_offset = 0;
   msg_size = 0;

   ZoO_strings_initialize(&string_);

   while (run)
   {
      if
      (
         ZoO_network_receive
         (
            &(s.network),
            cast(ulong*)&msg_offset,
            cast(ulong*)&msg_size,
            &msg_type
         ) == 0
      )
      {
         switch (msg_type)
         {
            case ZoO_msg_type.ZoO_JOIN:
               handle_user_join(s, &string_, msg_offset, msg_size);
               break;

            case ZoO_msg_type.ZoO_PRIVMSG:
               handle_message(s, &string_, msg_offset, msg_size);
               break;
            default: assert(0);
         }
      }
   }

   ZoO_strings_finalize(&string_);

   ZoO_network_disconnect(&(s.network));

   return 0;
}

extern(C) int main(const int argc, const char** argv)
{
   ZoO_state s = void;

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

   cast(void) finalize(&s);

   ZoO_S_DEBUG(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One terminated normally.");

   return 0;

   CRASH:
   {
      cast(void) finalize(&s);

      ZoO_S_DEBUG
      (
         ZoO_DEBUG_PROGRAM_FLOW,
         "Zero of One terminated by crashing."
      );

      return -1;
   }
}