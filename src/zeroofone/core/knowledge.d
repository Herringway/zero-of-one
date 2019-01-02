module zeroofone.core.knowledge;

import std.conv;
import std.experimental.logger;
import std.string;

import zeroofone.tool.strings;
import zeroofone.tool.sorted_list;
import zeroofone.pervasive;


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
	string word;
	ZoO_knowledge_special_effect special = ZoO_knowledge_special_effect.HAS_NO_EFFECT;
	size_t occurrences = 1;
	ZoO_knowledge_link[] forward_links;
	ZoO_knowledge_link[] backward_links;
}

struct ZoO_knowledge {
	size_t[] sorted_indices = [9, 2, 3, 4, 5, 6, 7, 1, 0, 8];
	ZoO_knowledge_word[] words = [
		ZoO_knowledge_word("START OF LINE", ZoO_knowledge_special_effect.STARTS_SENTENCE, 0, [], []),
		ZoO_knowledge_word("END OF LINE", ZoO_knowledge_special_effect.ENDS_SENTENCE, 0, [], []),
		ZoO_knowledge_word("!", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(",", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(".", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(":", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word(";", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word("?", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word("~", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], []),
		ZoO_knowledge_word("\x01", ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE, 0, [], [])
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
	int find(const string word, out size_t result) const @safe pure
	in(words.length > 0)
	out(; result <= words.length, text(result, " > ", words.length))
	{
		size_t r;

		if (ZoO_sorted_list_index_of!cmp_word(sorted_indices, word, this, r) == 0) {
			result = sorted_indices[r];

			return 0;
		}

		result = r;

		return -1;
	}

	size_t learn(const string word) @safe pure {
		import std.array : insertInPlace;
		size_t result;

		if (find(word, result) == 0) {
			words[result].occurrences += 1;

			debug(learning) tracef("Increased occurrences for word {'%s', occurrences: %s}", word, words[result].occurrences);
			return result;
		}

		words.length++;

		sorted_indices.insertInPlace(result, [words.length-1]);

		debug(learning) tracef("Learned word {'%s', id: %u, rank: %u}", word, words.length, result);

		result = words.length-1;

		words[$-1].word = word;

		return result;
	}
	void learnString(const string str) @safe {
		import zeroofone.core.assimilate : ZoO_knowledge_assimilate;
		ZoO_strings parsedString;
		parsedString.parse(str, ZoO_knowledge_punctuation_chars);
		ZoO_knowledge_assimilate(this, parsedString);
	}
}

@safe pure unittest {
	ZoO_knowledge knowledge;
	assert(knowledge.words[0].word == "START OF LINE");
	assert(knowledge.words[$-1].word == [ZoO_knowledge_punctuation_chars[$-1]]);
	size_t i = knowledge.learn("hello");
	assert(knowledge.words[i].word == "hello");
	assert(knowledge.words[i].occurrences == 1);
	knowledge.learn("word");
	knowledge.learn("hello");
	assert(knowledge.words[i].word == "hello");
	assert(knowledge.words[i].occurrences == 2);
	assert(i > 0);
	assert(knowledge.words[i-1].word != "hello");

	assert(knowledge.find("hello", i) == 0);
	assert(knowledge.words[i].word == "hello");

	assert(knowledge.find("hellp", i) == -1);
	assert(knowledge.words[i].word == "hello");

	assert(knowledge.sorted_indices == [9, 2, 3, 4, 5, 6, 7, 1, 0, 10, 11, 8]);
}

int cmp_word(const string word, const size_t sorted_index, const ZoO_knowledge other) @safe pure {
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