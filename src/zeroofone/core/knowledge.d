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
	bool find(const string word, out size_t result) const @safe pure
	in(words.length > 0)
	out(; result <= words.length, text(result, " > ", words.length))
	{
		size_t r;

		if (ZoO_sorted_list_index_of!cmp_word(sorted_indices, word, this, r) == 0) {
			result = sorted_indices[r];

			return true;
		}

		result = r;

		return false;
	}

	size_t learn(const string word) @safe pure {
		import std.array : insertInPlace;
		size_t result;

		if (find(word, result)) {
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
		assimilate(ZoO_strings(str));
	}

	void assimilate(const ZoO_strings string) @safe {
		size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence;
		size_t next_word, new_word;
		size_t new_word_id;

		debug(learning) trace("Learning phrase ", string);

		if (string.words.length == 0) {
			return;
		}

		init_sequence(string, sequence);

		add_word_occurrence(sequence);

		next_word = 0;
		new_word = ZoO_MARKOV_ORDER;

		while (next_word <= (string.words.length + ZoO_MARKOV_ORDER)) {
			if (new_word < string.words.length) {
				new_word_id = learn(string.words[new_word]);
			} else {
				new_word_id = ZoO_WORD_END_OF_LINE;
			}

			sequence = sequence[1..$]~0;

			sequence[ZoO_MARKOV_ORDER * 2] = new_word_id;

			add_word_occurrence(sequence);

			next_word += 1;
			new_word += 1;
		}
	}

	void add_word_occurrence(const size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence) @safe {
		import zeroofone.core.sequence : ZoO_knowledge_get_link;
		static void add_sequence(ref ZoO_knowledge_link[] links, const size_t[ZoO_MARKOV_ORDER] sequence, const size_t target_i, const size_t offset) @safe {
			const size_t[ZoO_SEQUENCE_SIZE] searchSeq = sequence[offset..offset+ZoO_SEQUENCE_SIZE];
			auto link_index = ZoO_knowledge_get_link(links, searchSeq);
			auto link = &links[link_index];

			foreach (i, target; link.targets) {
				if (target == sequence[target_i]) {
					link.targets_occurrences[i] += 1;

					return;
				}
			}

			link.targets.length += 1;
			link.targets[$ - 1] = sequence[target_i];
			link.targets_occurrences ~= 1;
		}
		auto word = &words[sequence[ZoO_MARKOV_ORDER]];

		add_sequence(word.forward_links, sequence[ZoO_MARKOV_ORDER + 1..$], ZoO_MARKOV_ORDER - 1, 0);
		add_sequence(word.backward_links, sequence[0..ZoO_MARKOV_ORDER], 0, 1);
	}


	void init_sequence(const ZoO_strings string, ref size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence) @safe {
		/* We are going to link this sequence to ZoO_WORD_START_OF_LINE */
		sequence[ZoO_MARKOV_ORDER] = ZoO_WORD_START_OF_LINE;

		foreach (i; 1..ZoO_MARKOV_ORDER+1) {
			sequence[ZoO_MARKOV_ORDER - i] = ZoO_WORD_START_OF_LINE;

			if (i <= string.words.length) {
				sequence[ZoO_MARKOV_ORDER + i] = learn(string.words[i - 1]);
			} else {
				sequence[ZoO_MARKOV_ORDER + i] = ZoO_WORD_END_OF_LINE;
			}
		}
	}
}
@safe unittest {
	ZoO_knowledge k;
	ZoO_strings str;
	size_t[(ZoO_MARKOV_ORDER * 2) + 1] seq;
	k.init_sequence(str, seq);
	assert(seq[0] == ZoO_WORD_START_OF_LINE);
	assert(seq[$-1] == ZoO_WORD_END_OF_LINE);
}
@safe unittest {
	ZoO_knowledge k;
	k.assimilate(ZoO_strings());
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

	assert(knowledge.find("hello", i));
	assert(knowledge.words[i].word == "hello");

	assert(!knowledge.find("hellp", i));
	assert(knowledge.words[i].word == "hello");

	assert(knowledge.sorted_indices == [9, 2, 3, 4, 5, 6, 7, 1, 0, 10, 11, 8]);
}

int cmp_word(const string word, const size_t sorted_index, const ZoO_knowledge other) @safe pure {
	import std.algorithm.comparison : cmp;
	return cmp(word, other.words[sorted_index].word);
}
