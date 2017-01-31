#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/index.h"

#include "../pipe/pipe.h"

#include "../knowledge/knowledge.h"

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
/*@
 @ requires (weights_sum > 0);
 @ requires \valid(weights);
 @ requires (\sum(0, (\length(weights) - 1), weights) = weights_sum);
@*/
static ZoO_index weighted_random_pick
(
   const ZoO_index weights [const restrict static 1],
   const ZoO_index weights_sum
)
{
   ZoO_index result, accumulator, random_number;

   accumulator = 0;

   random_number = ZoO_index_random_up_to(weights_sum);
   /*@ ensures (0 <= random_number <= weights_sum); @*/

   for (result = 0; accumulator < random_number; ++result)
   {
      /*@ requires (\sum(0, (\length(weights) - 1), weights) = weights_sum); @*/
      accumulator += weights[result];
   }

   return result;
}

/******************************************************************************/
/** ADDING ELEMENTS TO THE LEFT ***********************************************/
/******************************************************************************/

/*
 * Adds an id to the left of the sequence, according to what is known as likely
 * to fit there.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {*sequence} remains untouched.
 * Semaphore:
 *    Takes then releases access for {k}.
 * Returns:
 *    0 on success.
 *    -1 iff nothing fitting was found.
 *    -2 iff the addition of that id failed.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {k})
 *    (> {markov_order} 0)
 *    (initialized {*sequence[0..({markov_order} - 1)]})
 */
static int extend_left
(
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const ZoO_index markov_order,
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   const ZoO_index * restrict preceding_words;
   const ZoO_index * restrict preceding_words_weights;
   ZoO_index preceding_words_weights_sum;

   (void) ZoO_knowledge_lock_access(k, io);

   if
   (
      ZoO_knowledge_find_tws_targets
      (
         k,
         *sequence,
         markov_order,
         &preceding_words,
         &preceding_words_weights,
         &preceding_words_weights_sum,
         io
      ) < 0
   )
   {
      (void) ZoO_knowledge_unlock_access(k, io);

      return -1;
   }

   /* preceding_words_weights_sum > 0 */

   if
   (
      ZoO_sequence_append_left
      (
         weighted_random_pick
         (
            preceding_words_weights,
            preceding_words_weights_sum
         ),
         sequence,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      (void) ZoO_knowledge_unlock_access(k, io);

      return -3;
   }

   (void) ZoO_knowledge_unlock_access(k, io);

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
 *    (> {markov_order} 0)
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int complete_left_part_of_sequence
(
   ZoO_index * sequence [restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const ZoO_index markov_order,
   size_t credits [const restrict],
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   for (;;)
   {
      if ((credits == (size_t *) NULL) || (*credits > 0))
      {
         if
         (
            extend_left
            (
               sequence,
               sequence_capacity,
               sequence_length,
               markov_order,
               k,
               io
            ) < 0
         )
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

      if (credits != (size_t *) NULL)
      {
         *credits -= 1;
      }

      /* We are sure *sequence[0] is defined. */
      switch (*sequence[0])
      {
         case ZoO_END_OF_SEQUENCE_ID:
            ZoO_S_WARNING
            (
               io,
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
 * Adds an id to the right of the sequence, according to what is known as likely
 * to fit there.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {*sequence} remains untouched.
 * Semaphore:
 *    Takes then releases access for {k}.
 * Returns:
 *    0 on success.
 *    -1 iff nothing fitting was found.
 *    -2 iff the addition of that id failed.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {k})
 *    (> {markov_order} 0)
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int extend_right
(
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const ZoO_index markov_order,
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   const ZoO_index * restrict following_words;
   const ZoO_index * restrict following_words_weights;

   ZoO_index following_words_weights_sum;

   (void) ZoO_knowledge_lock_access(k, io);

   if
   (
      ZoO_knowledge_find_swt_targets
      (
         k,
         *sequence,
         *sequence_length,
         markov_order,
         &following_words,
         &following_words_weights,
         &following_words_weights_sum,
         io
      ) < 0
   )
   {
      (void) ZoO_knowledge_unlock_access(k, io);

      return -1;
   }

   /* following_words_weights_sum > 0 */

   if
   (
      ZoO_sequence_append_right
      (
         sequence,
         weighted_random_pick
         (
            following_words_weights,
            following_words_weights_sum
         ),
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      (void) ZoO_knowledge_unlock_access(k, io);

      return -3;
   }

   (void) ZoO_knowledge_unlock_access(k, io);

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
 *    (> {markov_order} 0)
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int complete_right_part_of_sequence
(
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const ZoO_index markov_order,
   size_t credits [const restrict],
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   for (;;)
   {
      if ((credits == (size_t *) NULL) || (*credits > 0))
      {
         if
         (
            extend_right
            (
               sequence,
               sequence_capacity,
               sequence_length,
               markov_order,
               k,
               io
            ) < 0
         )
         {
            /* Safe: (> sequence_length 1) */
            if (*sequence[(*sequence_length - 1)] == ZoO_END_OF_SEQUENCE_ID)
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
         *sequence[(*sequence_length - 1)] = ZoO_END_OF_SEQUENCE_ID;

         return 0;
      }

      if (credits != (size_t *) NULL)
      {
         *credits -= 1;
      }

      /* Safe: (> sequence_length 1) */
      switch (*sequence[(*sequence_length - 1)])
      {
         case ZoO_START_OF_SEQUENCE_ID:
            ZoO_S_WARNING
            (
               io,
               "END OF LINE was added at the right part of an sequence."
            );

            *sequence[(*sequence_length - 1)] = ZoO_END_OF_SEQUENCE_ID;
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
   struct ZoO_knowledge k [const static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   const ZoO_index * restrict swt_sequences_ref;
   const ZoO_index * restrict chosen_sequence;
   const ZoO_index * restrict swt_sequences_weights;
   ZoO_index swt_sequences_weights_sum;

   sequence[(markov_order - 1)] = initial_word;

   if (markov_order == 1)
   {
      return 0;
   }

   (void) ZoO_knowledge_lock_access(k, io);

   if
   (
      ZoO_knowledge_get_swt_sequences_ref
      (
         k,
         initial_word,
         &swt_sequences_ref,
         &swt_sequences_weights,
         &swt_sequences_weights_sum,
         io
      ) < 0
   )
   {
      (void) ZoO_knowledge_unlock_access(k, io);

      ZoO_S_ERROR
      (
         io,
         "Unable to find any sequence that would precede the initial word."
      );

      return -1;
   }

   /* following_sequences_ref contains only valid references. */
   (void) ZoO_knowledge_get_sequence
   (
      k,
      swt_sequences_ref
      [
         weighted_random_pick
         (
            swt_sequences_weights,
            swt_sequences_weights_sum
         )
      ],
      &chosen_sequence,
      io
   );

   /* Safe if 'allocate_initial_sequence' succeeded. */
   memcpy
   (
      (void *) sequence,
      (const void *) chosen_sequence,
      ((((size_t) markov_order) - 1) * sizeof(ZoO_index))
   );

   (void) ZoO_knowledge_unlock_access(k, io);

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

/* See "sequence.h" */
int ZoO_sequence_create_from
(
   const ZoO_index initial_word,
   size_t credits [const restrict],
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index markov_order,
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   if
   (
      ZoO_sequence_ensure_capacity
      (
         sequence,
         sequence_capacity,
         markov_order,
         io
      ) < 0
   )
   {
      *sequence_length = 0;

      return -1;
   }

   if
   (
      initialize_sequence
      (
         *sequence,
         initial_word,
         markov_order,
         k,
         io
      ) < 0
   )
   {
      *sequence_length = 0;

      return -2;
   }

   *sequence_length = markov_order;

   if
   (
      complete_right_part_of_sequence
      (
         sequence,
         sequence_capacity,
         sequence_length,
         markov_order,
         credits,
         k,
         io
      ) < 0
   )
   {
      *sequence_length = 0;

      return -3;
   }

   if
   (
      complete_left_part_of_sequence
      (
         sequence,
         sequence_capacity,
         sequence_length,
         markov_order,
         credits,
         k,
         io
      ) < 0
   )
   {
      *sequence_length = 0;

      return -4;
   }

   if (*sequence_length < 3)
   {
      /* 2 elements, for start and stop. */
      ZoO_S_ERROR(io, "Created sequence was empty.");

      *sequence_length = 0;

      return -5;
   }

   return 0;
}
