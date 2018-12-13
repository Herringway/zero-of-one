module core.knowledge;

import core.stdc.string;
import std.string;

import std.experimental.logger;

import tool.strings;
import tool.sorted_list;
import io.error;
import pervasive;


enum ZoO_WORD_START_OF_LINE = 0;
enum ZoO_WORD_END_OF_LINE = 1;

static if (ZoO_MARKOV_ORDER == 1) {
	enum ZoO_SEQUENCE_SIZE = 1;
} else {
	enum ZoO_SEQUENCE_SIZE = ZoO_MARKOV_ORDER - 1;
}

enum ZoO_S_LINK_SIZE = ZoO_SEQUENCE_SIZE + 1;

enum ZoO_knowledge_special_effect {
	HAS_NO_EFFECT,
	ENDS_SENTENCE,
	STARTS_SENTENCE,
	REMOVES_LEFT_SPACE,
	REMOVES_RIGHT_SPACE
}

struct ZoO_knowledge_link {
	ZoO_index[ZoO_SEQUENCE_SIZE] sequence;
	ZoO_index[] targets_occurrences;
	ZoO_index[] targets;
}

struct ZoO_knowledge_word {
	size_t word_size = 0;
	ZoO_char[] word = null;
	ZoO_knowledge_special_effect special = ZoO_knowledge_special_effect.HAS_NO_EFFECT;
	ZoO_index occurrences = 1;
	ZoO_index forward_links_count = 0;
	ZoO_index backward_links_count = 0;
	ZoO_knowledge_link* forward_links = null;
	ZoO_knowledge_link* backward_links = null;

	/*
	 * Frees all the memory used by {w}, but not {w} itself.
	 * The values of {w}'s members are set to reflect the changes.
	 */
	void finalize() {
		if (word != null) {
			word = null;
		}

		if (forward_links != null) {
			finalize_links(forward_links_count, forward_links);

			forward_links = null;
		}

		if (backward_links != null) {
			finalize_links(backward_links_count, backward_links);

			backward_links = null;
		}

		forward_links_count  = 0;
		backward_links_count = 0;
	}
}


struct ZoO_knowledge {
	ZoO_index[] sorted_indices;
	ZoO_knowledge_word[] words;

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
	int add_punctuation_nodes() {
		int error;
		char w;
		ZoO_index i, id;

		if (learn("START OF LINE", id) < 0) {
			critical("Could not add 'START OF LINE' to knowledge.");

			return -2;
		}

		words[id].special = ZoO_knowledge_special_effect.STARTS_SENTENCE;
		words[id].occurrences = 0;

		if (learn("END OF LINE", id) < 0) {
			critical("Could not add 'END OF LINE' to knowledge.");

			return -2;
		}

		words[id].special = ZoO_knowledge_special_effect.ENDS_SENTENCE;
		words[id].occurrences = 0;

		error = 0;

		for (i = 0; i < ZoO_knowledge_punctuation_chars.length; ++i) {
			w = ZoO_knowledge_punctuation_chars[i];

			if (learn([w], id) < 0) {
				warningf("Could not add '%s' to knowledge.", w);

				error = -1;
			} else {
				words[id].special = ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE;
				words[id].occurrences = 0;
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
	int initialize() {
		if (add_punctuation_nodes() < -1) {
			finalize();

			return -1;
		}

		return 0;
	}

	/*
	 * Frees all the memory used by {k}, but not {k} itself.
	 * The values of {k}'s members are set to reflect the changes.
	 */
	void finalize() {
		ZoO_index i;

		for (i = 0; i < words.length; ++i) {
			words[i].finalize();
		}
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
	int find(const ZoO_char[] word, out ZoO_index result) const {
		ZoO_index r;

		if (ZoO_sorted_list_index_of(cast(uint)words.length, sorted_indices.ptr, word.toStringz, ZoO_index.sizeof, &cmp_word, &this, &r) == 0) {
			result = sorted_indices[r];

			return 0;
		}

		result = r;

		return -1;
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
	int learn(const ZoO_char[] word, out ZoO_index result) {
		ZoO_index temp;

		if (find(word, result) == 0) {
			if (words[result].occurrences == ZoO_INDEX_MAX) {
				warningf("Maximum number of occurrences has been reached for word '"~ZoO_CHAR_STRING_SYMBOL~"'.", word);

				return -1;
			}

			/* overflow-safe: (< k.words[*result].occurrences ZoO_INDEX_MAX) */
			words[result].occurrences += 1;

			return 0;
		}

		if (words.length == ZoO_INDEX_MAX) {
			warning("Maximum number of words has been reached.");

			return -1;
		}

		words.length++;

		sorted_indices.length++;

		/* We can only move indices right of *result if they exist. */
		if (result < words.length-1) {
			/* TODO: check if correct. */
			memmove(sorted_indices.ptr + result + 1, sorted_indices.ptr + result, (words.length - result) * ZoO_index.sizeof);
		}

		temp = result;

		sorted_indices[result] = cast(uint)words.length-1;

		result = cast(uint)words.length-1;

		words[$-1].word = word.dup;

		tracef(ZoO_DEBUG_LEARNING, "Learned word {'%s', id: %u, rank: %u}", word, words.length, temp);

		return 0;
	}
}

unittest {
	ZoO_knowledge knowledge;
	knowledge.initialize();
	assert(knowledge.words[0].word == "START OF LINE");
	assert(knowledge.words[$-1].word == [ZoO_knowledge_punctuation_chars[$-1]]);
	ZoO_index i;
	knowledge.learn("hello", i);
	assert(knowledge.words[i].word == "hello");
	assert(knowledge.words[i].occurrences == 1);
	knowledge.learn("word", i);
	knowledge.learn("hello", i);
	assert(knowledge.words[i].word == "hello");
	assert(knowledge.words[i].occurrences == 2);
	assert(i > 0);
	assert(knowledge.words[i-1].word != "hello");

	knowledge.find("hello", i);
	assert(knowledge.words[i].word == "hello");
}

void finalize_links(const ZoO_index count, ZoO_knowledge_link* links) {
	ZoO_index i;
}

int cmp_word(const void* a, const void* b, const void* other) {
	const ZoO_char* word = cast(const ZoO_char*) a;
	const ZoO_index* sorted_index = cast(const ZoO_index*) b;
	const ZoO_knowledge* k = cast(ZoO_knowledge *) other;

	return strcmp(word, k.words[*sorted_index].word.toStringz);
}

immutable string ZoO_knowledge_punctuation_chars = [
		'!',
		',',
		'.',
		':',
		';',
		'?',
		'~',
		'\001'
	];

immutable string ZoO_knowledge_forbidden_chars = [
		'(',
		')',
		'[',
		']',
		'{',
		'}',
		'<',
		'>'
	];