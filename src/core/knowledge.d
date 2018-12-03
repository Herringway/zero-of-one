module core.knowledge;

import core.stdc.stdint;
import core.stdc.stdlib;
import core.stdc.string;

import tool.strings_types;
import core.knowledge_types;
import tool.sorted_list;
import io.error;
import pervasive;

extern(C):

/** Basic functions of the ZoO_knowledge structure ****************************/

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
int add_punctuation_nodes
(
   ZoO_knowledge* k
)
{
   int error;
   char[2] w;
   ZoO_index i, id;

   if (ZoO_knowledge_learn(k, "START OF LINE", &id) < 0)
   {
      ZoO_S_FATAL("Could not add 'START OF LINE' to knowledge.");

      return -2;
   }

   k.words[id].special = ZoO_knowledge_special_effect.ZoO_WORD_STARTS_SENTENCE;
   k.words[id].occurrences = 0;

   if (ZoO_knowledge_learn(k, "END OF LINE", &id) < 0)
   {
      ZoO_S_FATAL("Could not add 'END OF LINE' to knowledge.");

      return -2;
   }

   k.words[id].special = ZoO_knowledge_special_effect.ZoO_WORD_ENDS_SENTENCE;
   k.words[id].occurrences = 0;

   w[1] = '\0';

   error = 0;

   for (i = 0; i < ZoO_knowledge_punctuation_chars_count; ++i)
   {
      w[0] = ZoO_knowledge_punctuation_chars[i];

      if (ZoO_knowledge_learn(k, w.ptr, &id) < 0)
      {
         ZoO_WARNING("Could not add '%s' to knowledge.", w);

         error = -1;
      }
      else
      {
         k.words[id].special = ZoO_knowledge_special_effect.ZoO_WORD_REMOVES_LEFT_SPACE;
         k.words[id].occurrences = 0;
      }
   }

   return error;
}


/*
 * Initializes all of {k}'s members to sane values.
 *
 * When returning 0:
 *    Initial punctuation nodes (including the mandatory "START OF LINE" and
 *    "END OF LINE" ones) have successfully been added to {k}.
 *
 * When return -1:
 *    Something went wrong, leading to {k} not being safe for use.
 *    {k} has been finalized.
 */
int ZoO_knowledge_initialize (ZoO_knowledge* k)
{
   k.words_count = 0;
   k.words = null;
   k.sorted_indices = null;

   if (add_punctuation_nodes(k) < -1)
   {
      ZoO_knowledge_finalize(k);

      return -1;
   }

   return 0;
}


void finalize_links
(
   const ZoO_index count,
   ZoO_knowledge_link* links
)
{
   ZoO_index i;

   for (i = 0; i < count; ++i)
   {
      free(links[i].targets_occurrences);
      free(links[i].targets);
   }
}

/*
 * Frees all the memory used by {w}, but not {w} itself.
 * The values of {w}'s members are set to reflect the changes.
 */
void finalize_word
(
   ZoO_knowledge_word* w
)
{
   if (w.word != null)
   {
      free(w.word);

      w.word = null;
   }

   if (w.forward_links != null)
   {
      finalize_links(w.forward_links_count, w.forward_links);

      free(w.forward_links);

      w.forward_links = null;
   }

   if (w.backward_links != null)
   {
      finalize_links(w.backward_links_count, w.backward_links);

      free(w.backward_links);

      w.backward_links = null;
   }

   w.forward_links_count  = 0;
   w.backward_links_count = 0;
}

/*
 * Frees all the memory used by {k}, but not {k} itself.
 * The values of {k}'s members are set to reflect the changes.
 */
void ZoO_knowledge_finalize (ZoO_knowledge* k)
{
   ZoO_index i;

   for (i = 0; i < k.words_count; ++i)
   {
      finalize_word(k.words + i);
   }

   k.words_count = 0;

   if (k.words != null)
   {
      free(k.words);

      k.words = null;
   }

   if (k.sorted_indices != null)
   {
      free(k.sorted_indices);

      k.sorted_indices = null;
   }
}

int cmp_word
(
   const void* a,
   const void* b,
   const void* other
)
{
   const ZoO_char* word = cast(const ZoO_char*) a;
   const ZoO_index* sorted_index = cast(const ZoO_index*) b;
   const ZoO_knowledge* k = cast(ZoO_knowledge *) other;

   return strcmp
   (
      word,
      k.words[*sorted_index].word
   );
}


/*
 * When returning 0:
 *    {word} is in {k}.
 *    {word} is located at {k.words[*result]}.
 *
 * When returning -1:
 *    {word} is not in {k}.
 *    {*result} is where {word} was expected to be found in
 *    {k.sorted_indices}.
 */
int ZoO_knowledge_find
(
   const ZoO_knowledge* k,
   const ZoO_char* word,
   ZoO_index* result
)
{
   ZoO_index r;

   if
   (
      ZoO_sorted_list_index_of
      (
         k.words_count,
         k.sorted_indices,
         word,
         ZoO_index.sizeof,
         &cmp_word,
         k,
         &r
      )
      == 0
   )
   {
      *result = k.sorted_indices[r];

      return 0;
   }

   *result = r;

   return -1;
}

void word_init (ZoO_knowledge_word* w)
{
   w.word_size = 0;
   w.word = null;
   w.special = ZoO_knowledge_special_effect.ZoO_WORD_HAS_NO_EFFECT;
   w.occurrences = 1;
   w.forward_links_count  = 0;
   w.backward_links_count = 0;
   w.forward_links  = null;
   w.backward_links = null;
}

/*
 * When returning 0:
 *    {word} was either added to {k} or its representation in {k} has its
 *    occurrences count increased.
 *    {*result} indicates where {word} is in {k.words}.
 *
 * When returning -1:
 *    Something went wrong when adding the occurrence of {word} to {k}.
 *    {k} remains semantically unchanged.
 *    {*result} may or may not have been altered.
 */
int ZoO_knowledge_learn
(
   ZoO_knowledge* k,
   const ZoO_char* word,
   ZoO_index* result
)
{
   ZoO_knowledge_word * new_wordlist;
   ZoO_index * new_sorted_indices;
   ZoO_index temp;

   /* prevents k [restrict] */
   if (ZoO_knowledge_find(k, word, result) == 0)
   {
      if (k.words[*result].occurrences == ZoO_INDEX_MAX)
      {
         ZoO_WARNING
         (
            "Maximum number of occurrences has been reached for word '"~
            ZoO_CHAR_STRING_SYMBOL~
            "'.",
            word
         );

         return -1;
      }

      /* overflow-safe: (< k.words[*result].occurrences ZoO_INDEX_MAX) */
      k.words[*result].occurrences += 1;

      return 0;
   }

   if (k.words_count == ZoO_INDEX_MAX)
   {
      ZoO_S_WARNING("Maximum number of words has been reached.");

      return -1;
   }

   new_wordlist =
      cast(ZoO_knowledge_word *) realloc
      (
         k.words,
         (
            (
               /* overflow-safe: (< k.words_count ZoO_INDEX_MAX) */
               k.words_count + 1
            )
            * ZoO_knowledge_word.sizeof
         )
      );

   if (new_wordlist == null)
   {
      ZoO_ERROR
      (
         "Could not learn the word '%s': unable to realloc the word list.",
         word
      );

      return -1;
   }

   k.words = new_wordlist;

   new_sorted_indices =
      cast(ZoO_index *) realloc
      (
         k.sorted_indices,
         (
            (
               /* overflow-safe: (< k.words_count ZoO_INDEX_MAX) */
               k.words_count + 1
            )
            * ZoO_index.sizeof
         )
      );

   if (new_sorted_indices == null)
   {
      ZoO_ERROR
      (
         "Could not learn the word '"~
         ZoO_CHAR_STRING_SYMBOL~
         "': unable to realloc the index list.",
         word
      );

      return -1;
   }

   k.sorted_indices = new_sorted_indices;

   /* We can only move indices right of *result if they exist. */
   if (*result < k.words_count)
   {
      /* TODO: check if correct. */
      memmove
      (
         /*
          * Safe:
          *  (.
          *    (and
          *       (== (length k.sorted_indices) (+ k.words_count 1))
          *       (< *result k.words_count)
          *    )
          *    (< (+ *result 1) (length k.sorted_indices))
          * )
          */
         k.sorted_indices + *result + 1,
         /* Safe: see above */
         k.sorted_indices + *result,
         (
            (
               /* Safe: (< *result k.words_count) */
               k.words_count - *result
            )
            * ZoO_index.sizeof
         )
      );
   }

   temp = *result;

   k.sorted_indices[*result] = k.words_count;

   *result = k.words_count;

   word_init(k.words + *result);

   /* XXX: strlen assumed to work with ZoO_char. */
   k.words[*result].word_size = strlen(word);

   if (k.words[*result].word_size == SIZE_MAX)
   {
      ZoO_S_WARNING
      (
         "Could not learn word that had a size too big to store in a '\\0' "~
         "terminated string. Chances are, this is but a symptom of the real "~
         "problem."
      );

      return -1;
   }

   /* We also need '\0' */
   k.words[*result].word_size += 1;

   k.words[*result].word =
      cast(ZoO_char *) calloc
      (
         k.words[*result].word_size,
         ZoO_char.sizeof
      );

   if (k.words[*result].word == null)
   {
      ZoO_S_ERROR
      (
         "Could not learn word due to being unable to allocate the memory to "~
         "store it."
      );

      k.words[*result].word_size = 0;

      return -1;
   }

   memcpy(k.words[*result].word, word, k.words[*result].word_size);

   /* Safe: k.words_count < ZoO_INDEX_MAX */
   k.words_count += 1;

   ZoO_DEBUG
   (
      ZoO_DEBUG_LEARNING,
      "Learned word {'%s', id: %u, rank: %u}",
      word[0..strlen(word)],
      *result,
      temp
   );

   return 0;
}

/* XXX: are we as close to immutable as we want to be? */
const uint ZoO_knowledge_punctuation_chars_count = 8;
const ZoO_char[8] ZoO_knowledge_punctuation_chars =
   [
      '!',
      ',',
      '.',
      ':',
      ';',
      '?',
      '~',
      '\001'
   ];

/* XXX: are we as close to immutable as we want to be? */
const uint ZoO_knowledge_forbidden_chars_count = 8;
const ZoO_char[8] ZoO_knowledge_forbidden_chars =
   [
      '(',
      ')',
      '[',
      ']',
      '{',
      '}',
      '<',
      '>'
   ];