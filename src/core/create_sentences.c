#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../io/error.h"

#include "knowledge.h"

static ZoO_index pick_an_index
(
   ZoO_index const occurrences,
   const ZoO_index links_occurrences [const restrict static 1],
   const ZoO_index links [const restrict static 1]
)
{
   ZoO_index result, accumulator, random_number;

   result = 0;
   accumulator = links_occurrences[0];
   random_number = (((ZoO_index) rand()) % occurrences);

   while (accumulator < random_number)
   {

      /*
       * Should be safe:
       * result overflowing <-> sum('links_occurrences') > 'occurrences'
       * and sum('links_occurrences') == 'occurrences'
       */
      result += 1;

      /*
       * Should be safe:
       *  - sum('links_occurrences') == 'occurrences'.
       *  - 'occurrences' is safe.
       *  ----
       *  'accumulator' is safe.
       */
      accumulator += links_occurrences[result];
   }

   return links[result];
}

static unsigned char * extend_left
(
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_index word_id,
   ZoO_char current_sentence [static 1],
   size_t sentence_size [const restrict static 1],
   ZoO_index credits [const static 1]
)
{
   size_t addition_size;
   struct ZoO_knowledge_word * w;
   ZoO_char * next_sentence;

   w = (k->words + word_id);

   if
   (
      (w->special == ZoO_WORD_STARTS_SENTENCE)
      || (w->occurrences == 0)
   )
   {
      return current_sentence;
   }

   /* prevents current_sentence [restrict] */
   next_sentence = current_sentence;

   for (;;)
   {
      if (*credits == 0)
      {
         return current_sentence;
      }

      *credits -= 1;
      word_id =
         pick_an_index
         (
            w->occurrences,
            w->backward_links_occurrences,
            w->backward_links
         );

      w = (k->words + word_id);

      switch (w->special)
      {
         case ZoO_WORD_HAS_NO_EFFECT:
            /* FIXME: not overflow-safe. */
            /* word also contains an '\0', which we will replace by a ' ' */
            addition_size = w->word_size;
            break;

         case ZoO_WORD_ENDS_SENTENCE:
            ZoO_S_WARNING("END OF LINE should not be prefixable.");
            return current_sentence;

         case ZoO_WORD_STARTS_SENTENCE:
            return current_sentence;

         case ZoO_WORD_REMOVES_LEFT_SPACE:
         case ZoO_WORD_REMOVES_RIGHT_SPACE:
            /* word also contains an '\0', which we will remove. */
            addition_size = w->word_size - 1;
            break;
      }

      if (*sentence_size > (SIZE_MAX - addition_size))
      {
         ZoO_S_WARNING
         (
            "Sentence construction aborted to avoid size_t overflow."
         );

         return current_sentence;
      }

      next_sentence =
         (ZoO_char *) calloc
         (
            /* overflow-safe */
            (*sentence_size + addition_size),
            sizeof(ZoO_char)
         );

      if (next_sentence == (ZoO_char *) NULL)
      {
         ZoO_S_ERROR("Could not allocate memory to store new sentence.");

         return current_sentence;
      }

      /* overflow-safe */
      *sentence_size = (*sentence_size + addition_size);

      switch (w->special)
      {
         case ZoO_WORD_HAS_NO_EFFECT:
            snprintf
            (
               next_sentence,
               *sentence_size,
               " " ZoO_CHAR_STRING_SYMBOL ZoO_CHAR_STRING_SYMBOL,
               w->word,
               current_sentence
            );
            break;

         case ZoO_WORD_REMOVES_LEFT_SPACE:
            snprintf
            (
               next_sentence,
               *sentence_size,
               ZoO_CHAR_STRING_SYMBOL ZoO_CHAR_STRING_SYMBOL,
               w->word,
               current_sentence
            );
            break;

         case ZoO_WORD_REMOVES_RIGHT_SPACE:
            snprintf
            (
               next_sentence,
               *sentence_size,
               ZoO_CHAR_STRING_SYMBOL ZoO_CHAR_STRING_SYMBOL,
               w->word,
               /* Safe: strlen(current_sentence) >= 2 */
               (current_sentence + 1)
            );
            break;

         default:
            /* TODO: PROGRAM LOGIC ERROR */
            break;
      }

      free((void *) current_sentence);

      /* prevents current_sentence [const] */
      current_sentence = next_sentence;
   }
}

static unsigned char * extend_right
(
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_index word_id,
   ZoO_char current_sentence [static 1],
   size_t sentence_size [const restrict static 1],
   ZoO_index credits [const static 1]
)
{
   size_t addition_size;
   struct ZoO_knowledge_word * w;
   ZoO_char * next_sentence;

   w = (k->words + word_id);

   if
   (
      (w->special == ZoO_WORD_ENDS_SENTENCE)
      || (w->occurrences == 0)
   )
   {
      return current_sentence;
   }

   /* prevents current_sentence [restrict] */
   next_sentence = current_sentence;

   for (;;)
   {
      if (*credits == 0)
      {
         return current_sentence;
      }

      *credits -= 1;

      word_id =
         pick_an_index
         (
            w->occurrences,
            w->forward_links_occurrences,
            w->forward_links
         );

      w = (k->words + word_id);

      switch (w->special)
      {
         case ZoO_WORD_HAS_NO_EFFECT:
            /* FIXME: Assumed to be overflow-safe. */
            /* word also contains an '\0', which we will replace by a ' '. */
            addition_size = w->word_size;
            break;

         case ZoO_WORD_ENDS_SENTENCE:
            return current_sentence;

         case ZoO_WORD_STARTS_SENTENCE:
            ZoO_S_WARNING("START OF LINE should not be suffixable.");
            return current_sentence;

         case ZoO_WORD_REMOVES_LEFT_SPACE:
         case ZoO_WORD_REMOVES_RIGHT_SPACE:
            /* word also contains an '\0', which we will remove. */
            addition_size = w->word_size - 1;
            break;
      }

      if (*sentence_size > (SIZE_MAX - addition_size))
      {
         ZoO_S_WARNING
         (
            "Sentence construction aborted to avoid size_t overflow."
         );

         return current_sentence;
      }

      next_sentence =
         (ZoO_char *) calloc
         (
            /* overflow-safe */
            (*sentence_size + addition_size),
            sizeof(ZoO_char)
         );

      if (next_sentence == (ZoO_char *) NULL)
      {
         ZoO_S_ERROR("Could not allocate memory to store new sentence.");

         return current_sentence;
      }

      /* overflow-safe */
      *sentence_size = (*sentence_size + addition_size);

      switch (w->special)
      {
         case ZoO_WORD_REMOVES_LEFT_SPACE:
            printf
            (
               "current sentence:'%s', pointing at '%c'.\n",
               current_sentence,
               current_sentence[*sentence_size - addition_size - 2]
            );
            current_sentence[*sentence_size - addition_size - 2] = '\0';

         case ZoO_WORD_HAS_NO_EFFECT:
            snprintf
            (
               next_sentence,
               *sentence_size,
               ZoO_CHAR_STRING_SYMBOL ZoO_CHAR_STRING_SYMBOL " ",
               current_sentence,
               w->word
            );
            break;

         case ZoO_WORD_REMOVES_RIGHT_SPACE:
            snprintf
            (
               next_sentence,
               *sentence_size,
               ZoO_CHAR_STRING_SYMBOL ZoO_CHAR_STRING_SYMBOL,
               current_sentence,
               w->word
            );
            break;

         default:
            /* TODO: PROGRAM LOGIC ERROR */
            break;
      }

      free((void *) current_sentence);

      /* prevents current_sentence [const] */
      current_sentence = next_sentence;
   }
}

int ZoO_knowledge_extend
(
   struct ZoO_knowledge k [const static 1],
   const struct ZoO_strings string [const static 1],
   int const ignore_first_word,
   ZoO_char * result [const static 1]
)
{
   int word_found;
   size_t sentence_size;
   ZoO_index i, word_id, word_min_score, word_min_id, credits;

   word_found = 0;
   credits = ZoO_MAX_REPLY_WORDS;

   if (ignore_first_word)
   {
      i = 1;
   }
   else
   {
      i = 0;
   }

   for (; i < string->words_count; ++i)
   {
      /* prevents k [restrict] */
      if (ZoO_knowledge_find(k, string->words[i], &word_min_id) == 0)
      {
         word_found = 1;
         word_min_score = k->words[word_min_id].occurrences;

         break;
      }
   }

   if (word_found == 0)
   {
      word_min_id = (rand() % k->words_count);
      word_min_score = k->words[word_min_id].occurrences;
   }

   for (; i < string->words_count; ++i)
   {
      if
      (
         (ZoO_knowledge_find(k, string->words[i], &word_id) == 0)
         && (k->words[word_id].occurrences < word_min_score)
      )
      {
         word_min_score = k->words[word_id].occurrences;
         word_min_id = word_id;
      }
   }

   /* 3: 2 spaces + '\0' */
   /* FIXME: not overflow-safe */
   switch (k->words[word_min_id].special)
   {
      case ZoO_WORD_REMOVES_LEFT_SPACE:
      case ZoO_WORD_REMOVES_RIGHT_SPACE:
         /* word + ' ' + '\0' */
         sentence_size = (strlen(k->words[word_min_id].word) + 2);
         break;

      case ZoO_WORD_HAS_NO_EFFECT:
         /* word + ' ' * 2 + '\0' */
         sentence_size = (strlen(k->words[word_min_id].word) + 3);
         break;

      default:
         ZoO_WARNING
         (
            "'%s' was unexpectedly selected as pillar.",
            k->words[word_min_id].word
         );
         /* word + '[' + ']' + ' ' * 2 + '\0' */
         sentence_size = (strlen(k->words[word_min_id].word) + 5);
         break;
   }

   *result = (ZoO_char *) calloc(sentence_size, sizeof(ZoO_char));

   if (*result == (ZoO_char *) NULL)
   {
      ZoO_S_ERROR("Could not allocate memory to start sentence.");

      return -2;
   }

   switch (k->words[word_min_id].special)
   {
      case ZoO_WORD_REMOVES_LEFT_SPACE:
         snprintf
         (
            *result,
            sentence_size,
            ZoO_CHAR_STRING_SYMBOL " ",
            k->words[word_min_id].word
         );
         break;

      case ZoO_WORD_REMOVES_RIGHT_SPACE:
         snprintf
         (
            *result,
            sentence_size,
            " " ZoO_CHAR_STRING_SYMBOL,
            k->words[word_min_id].word
         );
         break;

      case ZoO_WORD_HAS_NO_EFFECT:
         snprintf
         (
            *result,
            sentence_size,
            " " ZoO_CHAR_STRING_SYMBOL " ",
            k->words[word_min_id].word
         );
         break;

      default:
         snprintf
         (
            *result,
            sentence_size,
            " [" ZoO_CHAR_STRING_SYMBOL "] ",
            k->words[word_min_id].word
         );
         break;
   }

   if ((word_min_score == 0) || (credits == 0))
   {
      return 0;
   }

   --credits;

   /* prevents result [restrict] */
   *result = extend_left(k, word_min_id, *result, &sentence_size, &credits);

   if (*result == (ZoO_char *) NULL)
   {
      return -2;
   }

   *result = extend_right(k, word_min_id, *result, &sentence_size, &credits);

   if (*result == (ZoO_char *) NULL)
   {
      return -2;
   }

   return 0;
}
