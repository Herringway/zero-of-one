#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../io/error.h"

#include "../core/index.h"
#include "../core/knowledge.h"

#include "sequence.h"

/*
 * Returns a randomly chosen index pointing to a element in {weights}.
 * The values of {weights} are used as weights to guide the choice.
 * Returns:
 *    Value in [0, (length weights)[.
 * Pre:
 *    (> weights_sum 0).
 *    (= (sum weights) weights_sum).
 */
static ZoO_index weighted_random_pick
(
   const ZoO_index weights [const restrict static 1],
   const ZoO_index weights_sum
)
{
   ZoO_index result, accumulator, random_number;

   accumulator = 0;

   /* Safe: Included in [0, weights_sum]. */
   random_number = ZoO_index_random_up_to(weights_sum);

   for (result = 0; accumulator < random_number; ++result)
   {
      /* Safe: (= (sum weights) weights_sum) */
      accumulator += weights[result];
   }

   return result;
}

/*
 * FIXME: This does not belong here.
 * Calculates the size the sentence will have upon addition of the word, taking
 * into account {effect}.
 * Returns:
 *    0 on success.
 *    -1 iff adding the word would overflow {sentence_size}.
 * Post:
 *    (initialized new_size)
 */
static int get_new_size
(
   const size_t word_size,
   const size_t sentence_size,
   const enum ZoO_knowledge_special_effect effect,
   size_t new_size [const restrict static 1]
)
{
   size_t added_size;

   switch (effect)
   {
      case ZoO_WORD_HAS_NO_EFFECT:
         /* word also contains an '\0', which we will replace by a ' ' */
         added_size = word_size;
         break;

      case ZoO_WORD_ENDS_SENTENCE:
      case ZoO_WORD_STARTS_SENTENCE:
         added_size = 0;
         break;

      case ZoO_WORD_REMOVES_LEFT_SPACE:
      case ZoO_WORD_REMOVES_RIGHT_SPACE:
         /* word also contains an '\0', which we will remove. */
         added_size = (word_size - 1);
         break;
   }

   if ((SIZE_MAX - word_size) > sentence_size)
   {
      /* New size Would overflow. */
      *new_size = sentence_size;

      return -1;
   }

   /* Safe: (=< SIZE_MAX (+ sentence_size added_size)) */
   *new_size = (sentence_size + added_size);

   return 0;
}

/******************************************************************************/
/** ADDING ELEMENTS TO THE LEFT ***********************************************/
/******************************************************************************/

/*
 * Adds an id to the left of the sequence.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {*sequence} remains untouched.
 * Returns:
 *    0 on success.
 *    -1 iff adding the word would cause an overflow.
 *    -2 iff memory allocation was unsuccessful.
 * Post:
 *    (initialized {sequence})
 *    (initialized {*sequence})
 */
static int left_append
(
   const ZoO_index word_id,
   ZoO_index * sequence [const restrict],
   const size_t sequence_size
)
{
   ZoO_index * new_sequence;

   if ((SIZE_MAX - sizeof(ZoO_index)) > sequence_size)
   {
      ZoO_S_ERROR
      (
         "Left side append aborted, as the new sequence's size would overflow."
      );

      return -1;
   }

   new_sequence = (ZoO_index *) malloc(sizeof(ZoO_index) + sequence_size);

   if (new_sequence == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR
      (
         "Left side append aborted, as memory for the new sequence could not be"
         " allocated."
      );

      return -2;
   }

   if (sequence_size > 0)
   {
      memcpy
      (
         (void *) (new_sequence + 1),
         (const void *) sequence,
         sequence_size
      );

      free((void *) sequence);
   }

   new_sequence[0] = word_id;

   *sequence = new_sequence;

   return 0;
}

/*
 * Adds an id to the left of the sequence, according to what is known as likely
 * to fit there.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {*sequence} remains untouched.
 * Returns:
 *    0 on success.
 *    -1 iff nothing fitting was found.
 *    -2 iff the addition of that id failed.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {k})
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int extend_left
(
   ZoO_index * sequence [const restrict static 1],
   const size_t sequence_size,
   const struct ZoO_knowledge k [const restrict static 1]
)
{
   const ZoO_index * restrict preceding_words;
   const ZoO_index * restrict preceding_words_weights;
   ZoO_index preceding_words_weights_sum;

   if
   (
      ZoO_knowledge_get_preceding_words
      (
         k,
         *sequence,
         &preceding_words,
         &preceding_words_weights,
         &preceding_words_weights_sum
      ) < 0
   )
   {
      return -1;
   }

   /* preceding_words_weights_sum > 0 */

   if
   (
      left_append
      (
         weighted_random_pick
         (
            preceding_words_weights,
            preceding_words_weights_sum
         ),
         sequence,
         sequence_size
      ) < 0
   )
   {
      return -3;
   }

   return 0;
}

/*
 * Continuously adds ids to the left of the sequence, according to what is known
 * as likely to fit there. If {credits} is NULL, it will stop upon reaching
 * the id indicating the start of a sequence, otherwise it will also limit to
 * {*credits} words added (including the one indicating the start of a
 * sequence).
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {sequence} remains unfreed.
 * Returns:
 *    0 on success.
 *    -1 iff we did not manage to have ZoO_START_OF_SEQUENCE_ID as a starting
 *       point. This cannot be caused by lack of {*credits}, but rather by a
 *       memory allocation problem or a more important issue in {k}. Indeed, it
 *       could mean we do not know any word preceding {*sequence[0]}, not even
 *       ZoO_START_OF_SEQUENCE_ID.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {sequence_size})
 *    (initialized {k})
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int complete_left_part_of_sequence
(
   ZoO_index * sequence [restrict static 1],
   size_t sequence_size [const restrict static 1],
   ZoO_index credits [const restrict],
   const struct ZoO_knowledge k [const restrict static 1]
)
{
   for (;;)
   {
      if ((credits == (ZoO_index *) NULL) || (*credits > 0))
      {
         if (extend_left(sequence, *sequence_size, k) < 0)
         {
            /* We are sure *sequence[0] is defined. */
            if (*sequence[0] == ZoO_START_OF_SEQUENCE_ID)
            {
               /*
                * We failed to add a word, but it was because none should have
                * been added.
                */
               return 0;
            }
            else
            {
               return -1;
            }
         }
      }
      else
      {
         /* No more credits available, the sequence will have to start here. */
         *sequence[0] = ZoO_START_OF_SEQUENCE_ID;

         return 0;
      }

      /*
       * Safe: if it was going to overflow, extend_left would have returned a
       * negative value, making this statement unreachable.
       */
      *sequence_size = (*sequence_size + sizeof(ZoO_index));

      if (credits != (ZoO_index *) NULL)
      {
         *credits -= 1;
      }

      /* We are sure *sequence[0] is defined. */
      switch (*sequence[0])
      {
         case ZoO_END_OF_SEQUENCE_ID:
            ZoO_S_WARNING
            (
               "END OF LINE was added at the left part of an sequence."
            );

            *sequence[0] = ZoO_START_OF_SEQUENCE_ID;
            return 0;

         case ZoO_START_OF_SEQUENCE_ID:
            return 0;

         default:
            break;
      }
   }
}

/******************************************************************************/
/** ADDING ELEMENTS TO THE RIGHT **********************************************/
/******************************************************************************/

/*
 * Adds an id to the right of the sequence.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {sequence} remain untouched.
 * Returns:
 *    0 on success.
 *    -1 iff adding the word would cause an overflow.
 *    -2 iff memory allocation was unsuccessful.
 * Post:
 *    (initialized {sequence})
 *    (initialized {*sequence})
 */
static int right_append
(
   ZoO_index * sequence [const restrict],
   const ZoO_index word_id,
   const size_t sequence_size,
   const ZoO_index sequence_length
)
{
   ZoO_index * new_sequence;

   if ((SIZE_MAX - sizeof(ZoO_index)) > sequence_size)
   {
      ZoO_S_ERROR
      (
         "Right side append aborted, as the new sequence's size would overflow."
      );

      return -1;
   }

   new_sequence =
      (ZoO_index *) realloc
      (
         sequence,
         (sequence_size + sizeof(ZoO_index))
      );

   if (new_sequence == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR
      (
         "Right side append aborted, as memory for the new sequence could not "
         "be allocated."
      );

      return -2;
   }

   new_sequence[sequence_length] = word_id;

   *sequence = new_sequence;

   return 0;
}

/*
 * Adds an id to the right of the sequence, according to what is known as likely
 * to fit there.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {*sequence} remains untouched.
 * Returns:
 *    0 on success.
 *    -1 iff nothing fitting was found.
 *    -2 iff the addition of that id failed.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {k})
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int extend_right
(
   ZoO_index * sequence [const restrict static 1],
   const size_t sequence_size,
   const ZoO_index sequence_length,
   const struct ZoO_knowledge k [const restrict static 1]
)
{
   const ZoO_index * restrict following_words;
   const ZoO_index * restrict following_words_weights;

   ZoO_index following_words_weights_sum;

   if
   (
      ZoO_knowledge_get_following_words
      (
         k,
         *sequence,
         sequence_length,
         &following_words,
         &following_words_weights,
         &following_words_weights_sum
      ) < 0
   )
   {
      return -1;
   }

   /* following_words_weights_sum > 0 */

   if
   (
      right_append
      (
         sequence,
         weighted_random_pick
         (
            following_words_weights,
            following_words_weights_sum
         ),
         sequence_size,
         sequence_length
      ) < 0
   )
   {
      return -3;
   }

   return 0;
}

/*
 * Continuously adds ids to the right of the sequence, according to what is
 * known as likely to fit there. If {credits} is NULL, it will stop upon
 * reaching the id indicating the end of a sequence, otherwise it will also
 * limit to {*credits} words added (including the one indicating the end of a
 * sequence).
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {sequence} remain untouched.
 * Returns:
 *    0 on success.
 *    -1 iff we did not manage to have ZoO_END_OF_SEQUENCE_ID as a stopping
 *       point. This cannot be caused by lack of {*credits}, but rather by a
 *       memory allocation problem or a more important issue in {k}. Indeed, it
 *       could mean we do not know any word following {*sequence[0]}, not even
 *       ZoO_END_OF_SEQUENCE_ID.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {*sequence_size})
 *    (initialized {k})
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int complete_right_part_of_sequence
(
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_size [const restrict static 1],
   ZoO_index credits [const restrict],
   const struct ZoO_knowledge k [const restrict static 1]
)
{
   ZoO_index sequence_length;

   sequence_length = (*sequence_size / sizeof(ZoO_index));

   for (;;)
   {
      if ((credits == (ZoO_index *) NULL) || (*credits > 0))
      {
         if (extend_right(sequence, *sequence_size, sequence_length, k) < 0)
         {
            /* Safe: (> sequence_length 1) */
            if (*sequence[(sequence_length - 1)] == ZoO_END_OF_SEQUENCE_ID)
            {
               /*
                * We failed to add a word, but it was because none should have
                * been added.
                */
               return 0;
            }
            else
            {
               return -1;
            }
         }
      }
      else
      {
         /* No more credits available, we end the sequence. */
         *sequence[(sequence_length - 1)] = ZoO_END_OF_SEQUENCE_ID;

         return 0;
      }

      /*
       * Safe: if it was going to overflow, extend_left would have returned a
       * negative value, making this statement unreachable.
       */
      *sequence_size = (*sequence_size + sizeof(ZoO_index));
      sequence_length += 1;

      if (credits != (ZoO_index *) NULL)
      {
         *credits -= 1;
      }

      /* Safe: (> sequence_length 1) */
      switch (*sequence[(sequence_length - 1)])
      {
         case ZoO_START_OF_SEQUENCE_ID:
            ZoO_S_WARNING
            (
               "END OF LINE was added at the right part of an sequence."
            );

            *sequence[(sequence_length - 1)] = ZoO_END_OF_SEQUENCE_ID;
            return 0;

         case ZoO_END_OF_SEQUENCE_ID:
            return 0;

         default:
            break;
      }
   }
}

/******************************************************************************/
/** INITIALIZING SEQUENCE *****************************************************/
/******************************************************************************/

/*
 * Allocates the memory required to store the initial sequence.
 * Returns:
 *    0 on success.
 *    -1 if this would require more memory than can indicate a size_t variable.
 *    -2 if the allocation failed.
 * Post:
 *    (initialized {*sequence})
 *    (initialized {*sequence_size})
 */
static int allocate_initial_sequence
(
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_size [const restrict static 1],
   const ZoO_index markov_order
)
{
   if ((SIZE_MAX / sizeof(ZoO_index)) > ((size_t) markov_order))
   {
      ZoO_S_ERROR
      (
         "Unable to store size of the initial sequence in a size_t variable."
         "Either reduce the size of a ZoO_index or the markovian order."
      );

      *sequence = (ZoO_index *) NULL;
      *sequence_size = 0;

      return -1;
   }

   *sequence_size = ((size_t) markov_order) * sizeof(ZoO_index);
   *sequence = (ZoO_index *) malloc(*sequence_size);

   if (*sequence == (void *) NULL)
   {
      *sequence_size = 0;

      ZoO_S_ERROR
      (
         "Unable to allocate the memory required for an new sequence."
      );

      return -2;
   }

   return 0;
}

/*
 * Initializes an pre-allocated sequence by filling it with {initial_word}
 * followed by a sequence of ({markov_order} - 1) words that is known to have
 * followed {initial_word} at least once. This sequence is chosen depending on
 * how often {k} indicates it has followed {initial_word}. Note that if
 * {markov_order} is 1, there is no sequence added, simply {initial_word}.
 * Returns:
 *    0 on success.
 *    -1 if no such sequence was found.
 * Pre:
 *    (size (= {sequence} {markov_order}))
 *    (initialized {k})
 *    (> markov_order 0)
 * Post:
 *    (initialized {sequence[0..(markov_order - 1)]})
 */
static int initialize_sequence
(
   ZoO_index sequence [const restrict static 1],
   const ZoO_index initial_word,
   const ZoO_index markov_order,
   const struct ZoO_knowledge k [const static 1]
)
{
   const ZoO_index * const restrict * restrict following_sequences;
   const ZoO_index * restrict following_sequences_weights;
   ZoO_index following_sequences_weights_sum;
   ZoO_index chosen_sequence;

   sequence[0] = initial_word;

   if (markov_order == 1)
   {
      return 0;
   }

   if
   (
      ZoO_knowledge_get_following_sequences
      (
         k,
         initial_word,
         &following_sequences,
         &following_sequences_weights,
         &following_sequences_weights_sum
      ) < 0
   )
   {
      ZoO_S_ERROR
      (
         "Unable to find any sequence that would precede the initial word."
      );

      return -1;
   }

   chosen_sequence =
      weighted_random_pick
      (
         following_sequences_weights,
         following_sequences_weights_sum
      );

   /* Safe if 'allocate_initial_sequence' succeeded. */
   memcpy
   (
      (void *) (sequence + 1),
      (const void *) (following_sequences + chosen_sequence),
      (((size_t) markov_order) - 1) * sizeof(ZoO_index)
   );

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

/* See "sequence.h" */
int ZoO_create_sequence_from
(
   const ZoO_index initial_word,
   ZoO_index credits [const restrict],
   const struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index markov_order,
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_size [const restrict static 1]
)
{
   if (allocate_initial_sequence(sequence, sequence_size, markov_order) < 0)
   {
      return -1;
   }

   if (initialize_sequence(*sequence, initial_word, markov_order, k) < 0)
   {
      free((void *) *sequence);
      *sequence_size = 0;

      return -2;
   }

   if
   (
      complete_right_part_of_sequence
      (
         sequence,
         sequence_size,
         credits,
         k
      ) < 0
   )
   {
      free((void *) *sequence);
      *sequence_size = 0;

      return -3;
   }

   if
   (
      complete_left_part_of_sequence
      (
         sequence,
         sequence_size,
         credits,
         k
      ) < 0
   )
   {
      free((void *) *sequence);
      *sequence_size = 0;

      return -4;
   }

   if ((*sequence_size / sizeof(ZoO_index)) < 3)
   {
      /* 2 elements, for start and stop. */
      ZoO_S_ERROR("Created sequence was empty.");

      free((void *) *sequence);
      *sequence_size = 0;

      return -5;
   }

   return 0;
}
