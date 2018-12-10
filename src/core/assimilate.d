module core.assimilate;

import core.stdc.stdlib;
import core.stdc.string;
import std.string;

import io.error;

import core.knowledge_types;
import core.knowledge;
import core.sequence;
import pervasive;
import tool.strings_types;

/** Functions to assimilate sentences using a ZoO_knowledge structure *********/

int add_sequence
(
   ZoO_index* links_count,
   ZoO_knowledge_link** links,
   const ZoO_index* sequence,
   const ZoO_index target_i,
   const ZoO_index offset
)
{
   ZoO_index link_index, i;
   ZoO_knowledge_link * link;
   ZoO_index * new_p;

   if
   (
      ZoO_knowledge_get_link
      (
         links_count,
         links,
         (sequence + offset),
         &link_index
      ) < 0
   )
   {
      return -1;
   }

   link = (*links + link_index);
   link.occurrences += 1;

   for (i = 0; i < link.targets.length; ++i)
   {
      if (link.targets[i] == sequence[target_i])
      {
         link.targets_occurrences[i] += 1;

         return 0;
      }
   }

   link.targets.length += 1;

   if (new_p == null)
   {
      link.targets.length -= 1;

      /* TODO: err. */
      return -1;
   }

   link.targets[link.targets.length - 1] = sequence[target_i];

   new_p =
      cast(ZoO_index *) realloc
      (
         link.targets_occurrences,
         (ZoO_index.sizeof * link.targets.length)
      );

   if (new_p == null)
   {
      link.targets.length -= 1;

      /* TODO: err. */
      return -1;
   }

   link.targets_occurrences = new_p;
   link.targets_occurrences[link.targets.length - 1] = 1;

   return 0;
}

int add_word_occurrence
(
   ZoO_knowledge* k,
   const ZoO_index[(ZoO_MARKOV_ORDER * 2) + 1] sequence
)
{
   ZoO_index w;
   int error;

   w = sequence[ZoO_MARKOV_ORDER];

   error =
      add_sequence
      (
         &(k.words[w].forward_links_count),
         &(k.words[w].forward_links),
         sequence.ptr + (ZoO_MARKOV_ORDER + 1),
         (ZoO_MARKOV_ORDER - 1),
         0
      );

   error =
      (
         add_sequence
         (
            &(k.words[w].backward_links_count),
            &(k.words[w].backward_links),
            sequence.ptr,
            0,
            1
         )
         | error
      );

   return error;
}


int should_assimilate
(
   ZoO_strings* string,
   const string[] aliases
)
{
   ZoO_index i;

   /* Don't assimilate empty strings. */
   if (string.words_count == 0)
   {
      return 0;
   }

   /* Don't assimilate things that start with our name. */
   for (i = 0; i < aliases.length; ++i)
   {
      if (strncmp(aliases[i].toStringz, string.words[0], strlen(aliases[i].toStringz)) == 0)
      {
         return 0;
      }
   }

   return 1;
}

int init_sequence
(
   ZoO_knowledge* k,
   ZoO_strings* string,
   ZoO_index[(ZoO_MARKOV_ORDER * 2) + 1] sequence
)
{
   ZoO_index i;

   /* We are going to link this sequence to ZoO_WORD_START_OF_LINE */
   sequence[ZoO_MARKOV_ORDER] = ZoO_WORD_START_OF_LINE;

   for (i = 1; i <= ZoO_MARKOV_ORDER; ++i)
   {
      sequence[ZoO_MARKOV_ORDER - i] = ZoO_WORD_START_OF_LINE;

      if (i <= string.words_count)
      {
         if
         (
            ZoO_knowledge_learn
            (
               k,
               string.words[i - 1],
               (sequence.ptr + (ZoO_MARKOV_ORDER + i))
            ) < 0
         )
         {
            return -1;
         }
      }
      else
      {
         sequence[ZoO_MARKOV_ORDER + i] = ZoO_WORD_END_OF_LINE;
      }
   }

   return 0;
}

int ZoO_knowledge_assimilate
(
   ZoO_knowledge* k,
   ZoO_strings* string,
   const string[] aliases
)
{
   int error;
   ZoO_index[(ZoO_MARKOV_ORDER * 2) + 1] sequence;
   ZoO_index next_word, new_word, new_word_id;

   if (!should_assimilate(string, aliases))
   {
      return 0;
   }

   if (init_sequence(k, string, sequence) < 0)
   {
      return -1;
   }

   if (add_word_occurrence(k, sequence) < 0)
   {
      error = -1;

      /* There's a pun... */
      ZoO_S_WARNING("Could not add a link between words.");

      return -1;
   }

   error = 0;

   next_word = 0;
   new_word = ZoO_MARKOV_ORDER;

   while (next_word <= (string.words_count + ZoO_MARKOV_ORDER))
   {
      if (new_word < string.words_count)
      {
         /* prevents words [restrict], k [restrict] */
         if (ZoO_knowledge_learn(k, string.words[new_word], &new_word_id) < 0)
         {
            return -1;
         }
      }
      else
      {
         new_word_id = ZoO_WORD_END_OF_LINE;
      }

      memmove
      (
         sequence.ptr,
         sequence.ptr + 1,
         /* Accepts 0. */
         (ZoO_index.sizeof * (ZoO_MARKOV_ORDER * 2))
      );

      sequence[ZoO_MARKOV_ORDER * 2] = new_word_id;

      if (add_word_occurrence(k, sequence) < 0)
      {
         error = -1;

         /* There's a pun... */
         ZoO_S_WARNING("Could not add a link between words.");

         return -1;
      }

      /*
       * Safe:
       *  - next_word < words_count
       *  - words_count =< ZoO_INDEX_MAX
       *  ----
       *  next_word < ZoO_INDEX_MAX
       */
      next_word += 1;
      new_word += 1;
   }

   return error;
}