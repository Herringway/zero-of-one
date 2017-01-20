#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/char.h"
#include "../core/index.h"

#include "../cli/cli.h"

#include "../knowledge/knowledge.h"

#include "sequence.h"

/* TODO */
static int add_word
(
   const ZoO_index word_id,
   const size_t destination_size,
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_char destination [const restrict static max_destination_length],
   size_t destination_used_size [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
	const ZoO_char * word;
	size_t word_size;

	(void) ZoO_knowledge_lock_access(k, io);
	ZoO_knowledge_get_word(k, word_id, &word, &word_size, io);
	(void) ZoO_knowledge_unlock_access(k, io);

	if ((destination_used_size + word_size) > max_destination_length)
	{
	}

	if
	(
		(word_size == 2)
		&& ZoO_char_is_punctuation(word[0])
	)
	{
		snprintf
		(
			(destination + *destination_used_size),
			word_size,
			ZoO_CHAR_STRING_SYMBOL,
			current_sentence
		);
	}
	else
	{
	}

   return 0;
}
/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int ZoO_sequence_to_undercase_string
(
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index sequence_length,
   const ZoO_index max_destination_length,
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_char destination [const restrict static max_destination_length],
   ZoO_index destination_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index i;
   const ZoO_index actual_length = (sequence_length - 1);

   for (i = 0; i < actual_length; ++i)
   {
      if
      (
         add_word
         (
            sequence[i],
            max_destination_length,
            k,
            destination,
            destination_length,
            io
         ) < 0
      )
      {
         *destination_length = 0;

         return -1;
      }
   }

   return 0;
}
