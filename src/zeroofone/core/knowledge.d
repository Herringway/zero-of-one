module zeroofone.core.knowledge;

import std.algorithm.searching : countUntil;
import std.conv;
import std.experimental.logger;
import std.string;

import zeroofone.core.sequence;
import zeroofone.tool.strings;
import zeroofone.tool.sorted_list;


enum SpecialEffect {
	HAS_NO_EFFECT,
	ENDS_SENTENCE,
	STARTS_SENTENCE,
	REMOVES_LEFT_SPACE,
	REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD,
	REMOVES_RIGHT_SPACE
}

struct KnowledgeLink {
	KnowledgeLinkSequence sequence;
	size_t[] targetsOccurrences;
	size_t[] targets;
}

struct KnowledgeWord {
	string word;
	SpecialEffect special = SpecialEffect.HAS_NO_EFFECT;
	size_t occurrences = 1;
	KnowledgeLink[] forwardLinks;
	KnowledgeLink[] backwardLinks;
}

/// Generate a default array of KnowledgeWords, mostly punctuation
auto generateDefaultWords() @safe pure {
	KnowledgeWord[] result;
	// The start of line entry, used as a stopping point when extending a sentence leftward
	result ~= KnowledgeWord("START OF LINE", SpecialEffect.STARTS_SENTENCE, 0, [], []);
	// The end of line entry, used as a stopping point when extending a sentence rightward
	result ~= KnowledgeWord("END OF LINE", SpecialEffect.ENDS_SENTENCE, 0, [], []);

	return result;
}

/// Generate a sorted index from an array of KnowledgeWords
auto generateDefaultSort(KnowledgeWord[] input) @safe pure {
	import std.algorithm.sorting : makeIndex;
	size_t[] index = new size_t[](input.length);
	makeIndex!((x,y) => x.word < y.word)(input, index);
	return index;
}

// Avoid circular reference (dmd bug?)
// These should be moved inside Knowledge if possible
private enum defaultWords = generateDefaultWords();
enum startOfLine = defaultWords.countUntil!((x,y) => x.word == y)("START OF LINE");
enum endOfLine = defaultWords.countUntil!((x,y) => x.word == y)("END OF LINE");
struct Knowledge {
	KnowledgeWord[] words = defaultWords;
	size_t[] sortedIndices = defaultWords.generateDefaultSort();
	public alias startOfLine = .startOfLine;
	public alias endOfLine = .endOfLine;

	/*
	 * When returning true:
	 *    {word} is in {k}.
	 *    {word} is located at {k.words[*result]}.
	 *
	 * When returning false:
	 *    {word} is not in {k}.
	 *    {*result} is where {word} was expected to be found in
	 *    {k.sortedIndices}.
	 */
	bool find(const string word, out size_t result) const @safe pure
	in(words.length > 0)
	out(; result <= words.length, text(result, " > ", words.length))
	{
		size_t r;

		static int cmpWord(const string word, const size_t sortedIndex, const Knowledge other) @safe pure {
			import std.algorithm.comparison : cmp;
			return cmp(word, other.words[sortedIndex].word);
		}

		if (binarySearch!cmpWord(sortedIndices, word, this, r) == 0) {
			result = sortedIndices[r];

			return true;
		}

		result = r;

		return false;
	}

	auto findWord(const string word) const @safe pure
	in(words.length > 0)
	{
		import std.exception : enforce;
		size_t r;
		enforce(find(word, r), "Word not found");
		return words[r];
	}

	size_t learn(const string word) @safe pure {
		import std.array : insertInPlace;
		import std.range : front;
		size_t result;

		if (find(word, result)) {
			words[result].occurrences += 1;

			debug(learning) tracef("Increased occurrences for word {'%s', occurrences: %s}", word, words[result].occurrences);
			return result;
		}

		words.length++;

		sortedIndices.insertInPlace(result, [words.length-1]);

		debug(learning) tracef("Learned word {'%s', id: %u, rank: %u}", word, words.length, result);

		result = words.length-1;

		words[$-1].word = word;
		words[$-1].special = word.front.specialEffect;

		return result;
	}
	void learnString(const string str) @safe {
		assimilate(Strings(str));
	}

	void assimilate(const Strings string) @safe {
		import zeroofone.core.sequence : getKnowledgeLinks;
		void addWordOccurrence(const SentenceSequence sequence) @safe {
			static void addSequence(ref KnowledgeLink[] links, const KnowledgeLinkSequence sequence, const size_t targetWord) @safe {
				const linkIndex = getKnowledgeLinks(links, sequence);
				auto link = &links[linkIndex];

				foreach (i, target; link.targets) {
					if (target == targetWord) {
						link.targetsOccurrences[i] += 1;
						return;
					}
				}

				link.targets.length += 1;
				link.targets[$ - 1] = targetWord;
				link.targetsOccurrences ~= 1;
			}
			addSequence(words[sequence.startPoint].forwardLinks, KnowledgeLinkSequence(sequence.secondHalf[0 .. $-1]), sequence.secondHalf[$-1]);
			addSequence(words[sequence.startPoint].backwardLinks, KnowledgeLinkSequence(sequence.firstHalf[1 .. $]), sequence.firstHalf[0]);
		}

		debug(learning) trace("Learning phrase ", string);

		if (string.words.length == 0) {
			return;
		}

		auto sequence = initSequence(string);

		addWordOccurrence(sequence);

		size_t nextWord = 0;
		size_t newWord = SentenceSequence.MarkovOrder;

		while (nextWord <= (string.words.length + SentenceSequence.MarkovOrder)) {
			const isValidWord = newWord < string.words.length;
			const size_t newWordID = isValidWord ? learn(string.words[newWord]) : endOfLine;

			sequence = sequence[1..$]~newWordID;

			addWordOccurrence(sequence);

			nextWord += 1;
			newWord += 1;
		}
	}

	auto initSequence(const Strings strings) @safe {
		SentenceSequence sequence;
		// We are going to link this sequence to startOfLine
		sequence[] = startOfLine;

		foreach (i; 1..SentenceSequence.MarkovOrder+1) {
			const validWord = i <= strings.words.length;
			sequence[SentenceSequence.MarkovOrder + i] = validWord ? learn(strings.words[i - 1]) : endOfLine;
		}
		return sequence;
	}
}
@safe unittest {
	import std.algorithm.iteration : map;
	import std.range : enumerate, iota;
	enum words = iota(0, SentenceSequence.MarkovOrder).map!(x => x.text);
	Knowledge k;
	const str = Strings(format!"%-(%s %)"(words));
	const seq = k.initSequence(str);
	foreach (word; seq.firstHalf) {
		assert(word == Knowledge.startOfLine);
	}
	size_t[6] w;
	foreach (idx, word; words.enumerate) {
		k.find(word, w[idx]);
	}
	assert(seq.secondHalf == w[0 .. SentenceSequence.MarkovOrder]);
}
@safe unittest {
	Knowledge k;
	k.assimilate(Strings());
}

@safe pure unittest {
	import std.exception : assertThrown;
	import std.algorithm.sorting : isSorted;
	import std.range : indexed;
	Knowledge knowledge;
	assert(knowledge.words[Knowledge.startOfLine].word == "START OF LINE");
	knowledge.learn("hello");
	with (knowledge.findWord("hello")) {
		assert(word == "hello");
		assert(occurrences == 1);
	}
	knowledge.learn("word");
	knowledge.learn("hello");
	with (knowledge.findWord("hello")) {
		assert(word == "hello");
		assert(occurrences == 2);
	}

	assertThrown(knowledge.findWord("hellp"));

	assert(indexed(knowledge.words, knowledge.sortedIndices).isSorted!((x,y) => x.word < y.word));
}
