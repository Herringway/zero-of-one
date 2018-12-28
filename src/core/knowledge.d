module core.knowledge;

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
	size_t[ZoO_SEQUENCE_SIZE] sequence;
	size_t[] targets_occurrences;
	size_t[] targets;
}

struct ZoO_knowledge_word {
	size_t word_size = 0;
	char[] word = null;
	ZoO_knowledge_special_effect special = ZoO_knowledge_special_effect.HAS_NO_EFFECT;
	size_t occurrences = 1;
	ZoO_knowledge_link[] forward_links = null;
	ZoO_knowledge_link[] backward_links = null;
}

struct ZoO_knowledge {
	size_t[] sorted_indices = [9, 2, 3, 4, 5, 6, 7, 1, 0, 8];
	ZoO_knowledge_word[] words = [
		ZoO_knowledge_word(0, "START OF LINE".dup, ZoO_knowledge_special_effect.STARTS_SENTENCE, 0, [], []),
		ZoO_knowledge_word(0, "END OF LINE".dup, ZoO_knowledge_special_effect.ENDS_SENTENCE, 0, [], []),
		ZoO_knowledge_word(0, "!".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(0, ",".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(0, ".".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(0, ":".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(0, ";".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(0, "?".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(0, "~".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(0, "\x01".dup, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], [])
	];

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
	int find(const char[] word, out size_t result) const @safe {
		size_t r;

		if (ZoO_sorted_list_index_of!cmp_word(sorted_indices, word, this, r) == 0) {
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
	int learn(const char[] word, out size_t result) @safe {
		import std.array : insertInPlace;
		size_t temp;

		if (find(word, result) == 0) {
			/* overflow-safe: (< k.words[*result].occurrences ZoO_INDEX_MAX) */
			words[result].occurrences += 1;

			return 0;
		}

		words.length++;

		sorted_indices.insertInPlace(result, [cast(uint)words.length-1]);

		result = words.length-1;

		words[$-1].word = word.dup;

		tracef(ZoO_DEBUG_LEARNING, "Learned word {'%s', id: %u, rank: %u}", word, words.length, temp);

		return 0;
	}
}

@safe unittest {
	ZoO_knowledge knowledge;
	assert(knowledge.words[0].word == "START OF LINE");
	assert(knowledge.words[$-1].word == [ZoO_knowledge_punctuation_chars[$-1]]);
	size_t i;
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
	assert(knowledge.sorted_indices == [9, 2, 3, 4, 5, 6, 7, 1, 0, 10, 11, 8]);
}

int cmp_word(const char[] word, const size_t sorted_index, const ZoO_knowledge other) @safe {
	import std.algorithm.comparison : cmp;
	return cmp(word, other.words[sorted_index].word);
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