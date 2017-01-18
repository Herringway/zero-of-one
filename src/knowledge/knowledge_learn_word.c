#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../cli/cli.h"

#include "knowledge.h"

/******************************************************************************/
/** INITIALIZING STRUCTURES ***************************************************/
/******************************************************************************/

static void initialize_sequence_collection
(
   struct ZoO_knowledge_sequence_collection c [const restrict static 1]
)
{
   c->sequences_ref = (ZoO_index *) NULL;
   c->sequences_ref_length = 0;
   c->sequences_ref_sorted = (ZoO_index *) NULL;
   c->occurrences = (ZoO_index *) NULL;
   c->targets = (ZoO_index **) NULL;
   c->targets_length = (ZoO_index *) NULL;
   c->targets_occurrences = (ZoO_index **) NULL;
}

static void initialize_word
(
   struct ZoO_knowledge_word w [const restrict static 1]
)
{
   w->word = (const ZoO_char *) NULL;
   w->word_size = 0;
   w->occurrences = 0;

   initialize_sequence_collection(&(w->followed));
   initialize_sequence_collection(&(w->preceded));
}

/******************************************************************************/
/** ALLOCATING MEMORY *********************************************************/
/******************************************************************************/
static ZoO_char * copy_word
(
   const ZoO_char original [const restrict static 1],
   const ZoO_index original_length
)
{
   ZoO_char * result;

   result =
      (ZoO_char *)
      calloc
      (
         (size_t) (original_length + 1),
         sizeof(ZoO_char)
      );

   if (result == (ZoO_char *) NULL)
   {
      ZoO_S_ERROR("Unable to allocate memory to store new word.");

      return (ZoO_char *) NULL;
   }

   memcpy
   (
      (void *) result,
      (const void *) original,
      (((size_t) original_length) * sizeof(ZoO_char))
   );

   result[original_length] = '\0';

   return 0;
}

static int reallocate_words_list
(
   struct ZoO_knowledge k [const restrict static 1]
)
{
   struct ZoO_knowledge_word * new_words;

   if
   (
      (SIZE_MAX / sizeof(struct ZoO_knowledge_word)) > (size_t) k->words_length
   )
   {
      ZoO_S_ERROR
      (
         "Unable to store the size of the words list, as it would overflow"
         "size_t variables."
      );

      return -1;
   }

   new_words =
      (struct ZoO_knowledge_word *) realloc
      (
         (void *) k->words,
         (((size_t) k->words_length) * sizeof(struct ZoO_knowledge_word))
      );

   if (new_words == (struct ZoO_knowledge_word *) NULL)
   {
      ZoO_S_ERROR
      (
         "Unable to allocate the memory required for the new words list."
      );

      return -1;
   }

   k->words = new_words;

   return 0;
}

static int reallocate_words_sorted_list
(
   struct ZoO_knowledge k [const restrict static 1]
)
{
   ZoO_index * new_words_sorted;

   /*
    * This has already been tested previously for a struct ZoO_knowledge_word,
    * whose size is bigger than a ZoO_index.
    * */
   /*
   if ((SIZE_MAX / sizeof(ZoO_index)) > (size_t) k->words_length)
   {
      ZoO_S_ERROR
      (
         "Unable to store the size of the sorted words list, as it would"
         " overflow size_t variables."
      );

      return -1;
   }
   */

   new_words_sorted =
      (ZoO_index *) realloc
      (
         (void *) k->words_sorted,
         (((size_t) k->words_length) * sizeof(ZoO_index))
      );

   if (new_words_sorted == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR
      (
         "Unable to allocate the memory required for the new sorted words list."
      );

      return -1;
   }

   k->words_sorted = new_words_sorted;

   return 0;
}

static void set_nth_word
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sorted_word_id,
   const ZoO_index word_id
)
{
   /* Safe: (> k->words_length 1) */
   if (sorted_word_id < (k->words_length - 1))
   {
      memmove
      (
         /* Safe: (=< (+ sorted_word_id 1) k->words_length) */
         (void *) (k->words_sorted + (sorted_word_id + 1)),
         (const void *) (k->words_sorted + sorted_word_id),
         ((k->words_length - 1) - sorted_word_id)
      );
   }

   k->words_sorted[sorted_word_id] = word_id;
}

static int add_word
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_char word [const restrict static 1],
   const ZoO_index word_length,
   const ZoO_index word_id,
   const ZoO_index sorted_word_id
)
{
   ZoO_char * stored_word;

   if (k->words_length == ZoO_INDEX_MAX)
   {
      ZoO_S_ERROR
      (
         "Unable to add word: the variable that stores the number of known "
         "words would overflow."
      );

      return -1;
   }

   stored_word = copy_word(word, word_length);

   if (stored_word == (ZoO_char *) NULL)
   {
      return -1;
   }

   k->words_length += 1;

   if (reallocate_words_list(k) < 0)
   {
      k->words_length -= 1;

      return -1;
   }

   initialize_word(k->words + word_id);

   k->words[word_id].word = stored_word;
   k->words[word_id].word_size = ((word_length + 1) * sizeof(ZoO_char));

   if (reallocate_words_sorted_list(k) < 0)
   {
      k->words_length -= 1;

      return -1;
   }

   set_nth_word(k, sorted_word_id, word_id);

   return -1;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int ZoO_knowledge_learn_word
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_char word [const restrict static 1],
   const ZoO_index word_length,
   ZoO_index word_id [const restrict static 1]
)
{
   ZoO_index sorted_id;

   if
   (
      ZoO_knowledge_find_word_id
      (
         k,
         word,
         (word_length * sizeof(ZoO_char)),
         word_id
      ) == 0
   )
   {
      return 0;
   }

   sorted_id = *word_id;
   *word_id = k->words_length;

   return add_word(k, word, word_length, *word_id, sorted_id);
}
