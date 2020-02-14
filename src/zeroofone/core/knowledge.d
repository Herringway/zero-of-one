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
	SENTENCE_TERMINATOR,
	REMOVES_LEFT_SPACE,
	REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD,
	REMOVES_RIGHT_SPACE,
	NO_SPACES
}

bool capitalizesNext(const SpecialEffect effect) @safe pure {
	final switch (effect) {
		case SpecialEffect.REMOVES_LEFT_SPACE:
			return false;
		case SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD:
			return true;
		case SpecialEffect.REMOVES_RIGHT_SPACE:
			return false;
		case SpecialEffect.NO_SPACES:
			return false;
		case SpecialEffect.HAS_NO_EFFECT:
			return false;
		case SpecialEffect.SENTENCE_TERMINATOR:
			assert(0, "SENTENCE_TERMINATOR should not be found in sentences.");
	}
}
bool hasTrailingSpace(const SpecialEffect effect) @safe pure {
	final switch (effect) {
		case SpecialEffect.REMOVES_LEFT_SPACE:
			return true;
		case SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD:
			return true;
		case SpecialEffect.REMOVES_RIGHT_SPACE:
			return false;
		case SpecialEffect.NO_SPACES:
			return false;
		case SpecialEffect.HAS_NO_EFFECT:
			return true;
		case SpecialEffect.SENTENCE_TERMINATOR:
			assert(0, "SENTENCE_TERMINATOR should not be found in sentences.");
	}
}
bool useTrailingSpace(const SpecialEffect effect) @safe pure {
	final switch (effect) {
		case SpecialEffect.REMOVES_LEFT_SPACE:
			return false;
		case SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD:
			return false;
		case SpecialEffect.REMOVES_RIGHT_SPACE:
			return true;
		case SpecialEffect.NO_SPACES:
			return false;
		case SpecialEffect.HAS_NO_EFFECT:
			return true;
		case SpecialEffect.SENTENCE_TERMINATOR:
			assert(0, "SENTENCE_TERMINATOR should not be found in sentences.");
	}
}

immutable string knowledgePunctuationCharsRemovesLeftSpace = [
	',',
	':',
	';',
	'~',
	')'
];
immutable string knowledgePunctuationCharsRemovesRightSpace = [
	'('
];

immutable string knowledgePunctuationCharsNextCapitalized = [
	'?',
	'!',
	'.'
];

SpecialEffect specialEffect(dchar c) @safe pure {
	import std.algorithm.searching : canFind;
	import std.uni : isPunctuation;
	if (c.isPunctuation) {
		if (knowledgePunctuationCharsNextCapitalized.canFind(c)) {
			return SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD;
		}
		if (knowledgePunctuationCharsRemovesLeftSpace.canFind(c)) {
			return SpecialEffect.REMOVES_LEFT_SPACE;
		}
		if (knowledgePunctuationCharsRemovesRightSpace.canFind(c)) {
			return SpecialEffect.REMOVES_RIGHT_SPACE;
		}
		return SpecialEffect.NO_SPACES;
	}
	return SpecialEffect.HAS_NO_EFFECT;
}

struct KnowledgeLink {
	KnowledgeLinkSequence sequence;
	size_t[] targetsOccurrences;
	size_t[] targets;
}

struct KnowledgeWord {
	string word;
	SpecialEffect special = SpecialEffect.HAS_NO_EFFECT;
	size_t occurrences = 0;
	KnowledgeLink[] forwardLinks;
	KnowledgeLink[] backwardLinks;
	bool isTerminator() const @safe pure {
		return special == SpecialEffect.SENTENCE_TERMINATOR;
	}
}

/// Generate a default array of KnowledgeWords, mostly punctuation
auto generateDefaultWords() @safe pure {
	return [
		// The start/end of line entry, used as a stopping point when extending a sentence
		KnowledgeWord("", SpecialEffect.SENTENCE_TERMINATOR, 0, [], [])
	];
}

// Avoid circular reference (dmd bug?)
// These should be moved inside Knowledge if possible
private enum defaultWords = generateDefaultWords();
enum terminator = defaultWords.countUntil!((x,y) => x.special == y)(SpecialEffect.SENTENCE_TERMINATOR);
struct Knowledge {
	private KnowledgeWord[] words = generateDefaultWords();
	private size_t[string] wordMap;
	public alias terminator = .terminator;

	auto findNew(const string word) const @safe pure
	in(words.length > 0)
	out(result; result.isNull || result.get() <= words.length)
	{
		import std.typecons : nullable;
		if (auto foundWord = word in wordMap) {
			return nullable(*foundWord);
		}

		return typeof(return).init;
	}

	size_t learn(const string word) @safe pure {
		import std.range : front;

		const index = wordMap.require(word, words.length);
		if (index == words.length) {
			debug(learning) tracef("Learned word {'%s', id: %u, rank: %u}", word, words.length, index);
			words ~= KnowledgeWord(word, word.front.specialEffect);
		}

		words[index].occurrences += 1;

		debug(learning) tracef("Increased occurrences for word {'%s', occurrences: %s}", word, words[index].occurrences);
		return index;
	}
	void learnString(const string str) @safe {
		assimilate(Strings(str));
	}

	void assimilate(const Strings strings) @safe {
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

				link.targets ~= targetWord;
				link.targetsOccurrences ~= 1;
			}
			addSequence(words[sequence.startPoint].forwardLinks, KnowledgeLinkSequence(sequence.secondHalf[0 .. $-1]), sequence.secondHalf[$-1]);
			addSequence(words[sequence.startPoint].backwardLinks, KnowledgeLinkSequence(sequence.firstHalf[1 .. $]), sequence.firstHalf[0]);
		}

		debug(learning) trace("Learning phrase ", strings);

		if (strings.words.length == 0) {
			return;
		}

		auto sequence = initSequence(strings);

		addWordOccurrence(sequence);

		size_t nextWord = 0;
		size_t newWord = SentenceSequence.MarkovOrder;

		while (nextWord <= (strings.words.length + SentenceSequence.MarkovOrder)) {
			const isValidWord = newWord < strings.words.length;
			const size_t newWordID = isValidWord ? learn(strings.words[newWord]) : terminator;

			sequence = sequence[1..$]~newWordID;

			addWordOccurrence(sequence);

			nextWord += 1;
			newWord += 1;
		}
	}

	auto initSequence(const Strings strings) @safe {
		SentenceSequence sequence;

		foreach (i, ref word; sequence[SentenceSequence.MarkovOrder + 1..$]) {
			const validWord = i < strings.words.length;
			word = validWord ? learn(strings.words[i]) : terminator;
		}
		return sequence;
	}
	auto opIndex(size_t i) @safe const {
		return words[i];
	}
	auto length() @safe const {
		return words.length;
	}
	auto pickRandom() @safe const
	in(words.length > 0)
	{
		import std.algorithm.iteration : filter;
		import std.random : randomCover;
		import std.range : iota;
		return iota(0, words.length - 1).randomCover().filter!(x => x != terminator).front;
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
		assert(word == Knowledge.terminator);
	}
	size_t[6] w;
	foreach (idx, word; words.enumerate) {
		w[idx] = k.findNew(word).get;
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
	assert(knowledge.words[Knowledge.terminator].word == "");
	knowledge.learn("hello");
	with (knowledge[knowledge.findNew("hello").get]) {
		assert(word == "hello");
		assert(occurrences == 1);
	}
	knowledge.learn("word");
	knowledge.learn("hello");
	with (knowledge[knowledge.findNew("hello").get]) {
		assert(word == "hello");
		assert(occurrences == 2);
	}

	assert(knowledge.findNew("hellp").isNull);
}
