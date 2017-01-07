#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../io/error.h"
#include "../tool/sorted_list.h"

#include "knowledge.h"

/** Basic functions of the ZoO_knowledge structure ****************************/

/* See "knowledge.h". */
int ZoO_knowledge_find
(
   const struct ZoO_knowledge k [const restrict static 1],
   const ZoO_char word [const restrict static 1],
   ZoO_index result [const restrict static 1]
)
{
   ZoO_index r;

   if
   (
      ZoO_sorted_list_index_of
      (
         k->words_count,
         (void const *) k->sorted_indices,
         (void const *) word,
         sizeof(ZoO_index),
         cmp_word,
         (void const *) k,
         &r
      )
      == 0
   )
   {
      *result = k->sorted_indices[r];

      return 0;
   }

   *result = r;

   return -1;
}

static void word_init (struct ZoO_knowledge_word w [const restrict static 1])
{
   w->word_size = 0;
   w->word = (ZoO_char *) NULL;
   w->special = ZoO_WORD_HAS_NO_EFFECT;
   w->occurrences = 1;
   w->forward_links_count  = 0;
   w->backward_links_count = 0;
   w->forward_links  = (struct ZoO_knowledge_link *) NULL;
   w->backward_links = (struct ZoO_knowledge_link *) NULL;
}

/*
 * When returning 0:
 *    All punctuation symbols were added to {k}.
 * When returning -1:
 *    The mandatory punctuation symbols have been added to {k}, but some of the
 *    additional ones did not. This does not prevent ZoO from working, but
 *    will result in some punctuation symbols to be handled exactly like
 *    common words.
 * When returning -2:
 *    The mandatory punctuation symbols have not added to {k}. ZoO will not be
 *    able to work.
 */
static int add_punctuation_nodes
(
   struct ZoO_knowledge k [const static 1]
)
{
   int error;
   char w[2];
   ZoO_index i, id;

   if (ZoO_knowledge_learn(k, "START OF LINE", &id) < 0)
   {
      ZoO_S_FATAL("Could not add 'START OF LINE' to knowledge.");

      return -2;
   }

   k->words[id].special = ZoO_WORD_STARTS_SENTENCE;
   k->words[id].occurrences = 0;

   if (ZoO_knowledge_learn(k, "END OF LINE", &id) < 0)
   {
      ZoO_S_FATAL("Could not add 'END OF LINE' to knowledge.");

      return -2;
   }

   k->words[id].special = ZoO_WORD_ENDS_SENTENCE;
   k->words[id].occurrences = 0;

   w[1] = '\0';

   error = 0;

   for (i = 0; i < ZoO_knowledge_punctuation_chars_count; ++i)
   {
      w[0] = ZoO_knowledge_punctuation_chars[i];

      if (ZoO_knowledge_learn(k, w, &id) < 0)
      {
         ZoO_WARNING("Could not add '%s' to knowledge.", w);

         error = -1;
      }
      else
      {
         k->words[id].special = ZoO_WORD_REMOVES_LEFT_SPACE;
         k->words[id].occurrences = 0;
      }
   }

   return error;
}

/* See "knowledge.h" */
int ZoO_knowledge_initialize (struct ZoO_knowledge k [const static 1])
{
   k->words_count = 0;
   k->words = (struct ZoO_knowledge_word *) NULL;
   k->sorted_indices = (ZoO_index *) NULL;

   if (add_punctuation_nodes(k) < -1)
   {
      ZoO_knowledge_finalize(k);

      return -1;
   }

   return 0;
}

static void finalize_links
(
   ZoO_index const count,
   struct ZoO_knowledge_link links [const restrict static count]
)
{
   ZoO_index i;

   for (i = 0; i < count; ++i)
   {
      free((void *) links[i].targets_occurrences);
      free((void *) links[i].targets);
   }
}

/*
 * Frees all the memory used by {w}, but not {w} itself.
 * The values of {w}'s members are set to reflect the changes.
 */
static void finalize_word
(
   struct ZoO_knowledge_word w [const restrict static 1]
)
{
   if (w->word != (ZoO_char *) NULL)
   {
      free((void *) w->word);

      w->word = (ZoO_char *) NULL;
   }

   if (w->forward_links != (struct ZoO_knowledge_link *) NULL)
   {
      finalize_links(w->forward_links_count, w->forward_links);

      free((void *) w->forward_links);

      w->forward_links = (struct ZoO_knowledge_link *) NULL;
   }

   if (w->backward_links != (struct ZoO_knowledge_link *) NULL)
   {
      finalize_links(w->backward_links_count, w->backward_links);

      free((void *) w->backward_links);

      w->backward_links = (struct ZoO_knowledge_link *) NULL;
   }

   w->forward_links_count  = 0;
   w->backward_links_count = 0;
}

/* See "knowledge.h" */
void ZoO_knowledge_finalize (struct ZoO_knowledge k [const restrict static 1])
{
   ZoO_index i;

   for (i = 0; i < k->words_count; ++i)
   {
      finalize_word(k->words + i);
   }

   k->words_count = 0;

   if (k->words != (struct ZoO_knowledge_word *) NULL)
   {
      free((void *) k->words);

      k->words = (struct ZoO_knowledge_word *) NULL;
   }

   if (k->sorted_indices != (ZoO_index *) NULL)
   {
      free((void *) k->sorted_indices);

      k->sorted_indices = (ZoO_index *) NULL;
   }
}

/* See "knowledge.h" */
int ZoO_knowledge_learn
(
   struct ZoO_knowledge k [const static 1],
   const ZoO_char word [const restrict static 1],
   ZoO_index result [const restrict static 1]
)
{
   struct ZoO_knowledge_word * new_wordlist;
   ZoO_index * new_sorted_indices;
   ZoO_index temp;

   /* prevents k [restrict] */
   if (ZoO_knowledge_find(k, word, result) == 0)
   {
      if (k->words[*result].occurrences == ZoO_INDEX_MAX)
      {
         ZoO_WARNING
         (
            "Maximum number of occurrences has been reached for word '"
            ZoO_CHAR_STRING_SYMBOL
            "'.",
            word
         );

         return -1;
      }

      /* overflow-safe: (< k->words[*result].occurrences ZoO_INDEX_MAX) */
      k->words[*result].occurrences += 1;

      return 0;
   }

   if (k->words_count == ZoO_INDEX_MAX)
   {
      ZoO_S_WARNING("Maximum number of words has been reached.");

      return -1;
   }

   new_wordlist =
      (struct ZoO_knowledge_word *) realloc
      (
         (void *) k->words,
         (
            (
               /* overflow-safe: (< k->words_count ZoO_INDEX_MAX) */
               (size_t) (k->words_count + 1)
            )
            * sizeof(struct ZoO_knowledge_word)
         )
      );

   if (new_wordlist == (struct ZoO_knowledge_word *) NULL)
   {
      ZoO_ERROR
      (
         "Could not learn the word '%s': unable to realloc the word list.",
         word
      );

      return -1;
   }

   k->words = new_wordlist;

   new_sorted_indices =
      (ZoO_index *) realloc
      (
         (void *) k->sorted_indices,
         (
            (
               /* overflow-safe: (< k->words_count ZoO_INDEX_MAX) */
               (size_t) (k->words_count + 1)
            )
            * sizeof(ZoO_index)
         )
      );

   if (new_sorted_indices == (ZoO_index *) NULL)
   {
      ZoO_ERROR
      (
         "Could not learn the word '"
         ZoO_CHAR_STRING_SYMBOL
         "': unable to realloc the index list.",
         word
      );

      return -1;
   }

   k->sorted_indices = new_sorted_indices;

   /* We can only move indices right of *result if they exist. */
   if (*result < k->words_count)
   {
      /* TODO: check if correct. */
      memmove
      (
         /*
          * Safe:
          *  (->
          *    (and
          *       (== (length k->sorted_indices) (+ k->words_count 1))
          *       (< *result k->words_count)
          *    )
          *    (< (+ *result 1) (length k->sorted_indices))
          * )
          */
         (void *) (k->sorted_indices + *result + 1),
         /* Safe: see above */
         (const void *) (k->sorted_indices + *result),
         (
            (
               /* Safe: (< *result k->words_count) */
               (size_t) (k->words_count - *result)
            )
            * sizeof(ZoO_index)
         )
      );
   }

   temp = *result;

   k->sorted_indices[*result] = k->words_count;

   *result = k->words_count;

   word_init(k->words + *result);

   /* XXX: strlen assumed to work with ZoO_char. */
   k->words[*result].word_size = strlen(word);

   if (k->words[*result].word_size == SIZE_MAX)
   {
      ZoO_S_WARNING
      (
         "Could not learn word that had a size too big to store in a '\\0' "
         "terminated string. Chances are, this is but a symptom of the real "
         "problem."
      );

      return -1;
   }

   /* We also need '\0' */
   k->words[*result].word_size += 1;

   k->words[*result].word =
      (ZoO_char *) calloc
      (
         k->words[*result].word_size,
         sizeof(ZoO_char)
      );

   if (k->words[*result].word == (ZoO_char *) NULL)
   {
      ZoO_S_ERROR
      (
         "Could not learn word due to being unable to allocate the memory to "
         "store it."
      );

      k->words[*result].word_size = 0;

      return -1;
   }

   memcpy(k->words[*result].word, word, k->words[*result].word_size);

   /* Safe: k->words_count < ZoO_INDEX_MAX */
   k->words_count += 1;

   ZoO_DEBUG
   (
      ZoO_DEBUG_LEARNING,
      "Learned word {'%s', id: %u, rank: %u}",
      word,
      *result,
      temp
   );

   return 0;
}

