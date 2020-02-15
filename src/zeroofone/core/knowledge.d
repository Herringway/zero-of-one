module zeroofone.core.knowledge;

import std.algorithm.searching : countUntil;
import std.conv;
import std.experimental.logger;
import std.string;

import zeroofone.core.sequence;

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

immutable wstring knowledgePunctuationCharsRemovesLeftSpace = [
	',',
	':',
	';',
	'~',
	')',
	']',
	'}',
	'”'
];
immutable wstring knowledgePunctuationCharsRemovesRightSpace = [
	'(',
	'[',
	'{',
	'#',
	'“'
];

immutable wstring knowledgePunctuationCharsNextCapitalized = [
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

struct KnowledgeLinks {
	private KnowledgeLink[KnowledgeLinkSequence] links;
	auto ref learn(const KnowledgeLinkSequence sequence) @safe pure {
		return links.require(sequence, KnowledgeLink(sequence));
	}
	auto findSequence(const KnowledgeLinkSequence sequence) const @safe pure {
		import std.typecons : nullable;
		if (auto foundSeq = sequence in links) {
			return nullable(*foundSeq);
		}

		return typeof(return).init;
	}
	auto length() const @safe pure {
		return links.length;
	}
	auto randomLink() const @safe {
		import std.random : uniform;
		import std.range : popFrontN;
		auto values = links.byValue;
		values.popFrontN(uniform(0, links.length));
		return values.front;
	}
	void optimize() /*@safe*/ pure {
		links.rehash();
	}
}

@safe unittest {
	with(KnowledgeLinks()) {
		assert(learn(KnowledgeLinkSequence([10, 11])) == KnowledgeLink(KnowledgeLinkSequence([10,11])));
		assert(learn(KnowledgeLinkSequence([1,1])) == KnowledgeLink(KnowledgeLinkSequence([1,1])));
		assert(!findSequence(KnowledgeLinkSequence([1, 1])).isNull);
		assert(!findSequence(KnowledgeLinkSequence([10, 11])).isNull);
	}
}

struct KnowledgeWord {
	string word;
	SpecialEffect special = SpecialEffect.HAS_NO_EFFECT;
	size_t occurrences = 0;
	KnowledgeLinks forwardLinks;
	KnowledgeLinks backwardLinks;
	bool isTerminator() const @safe pure {
		return special == SpecialEffect.SENTENCE_TERMINATOR;
	}
}

/// Generate a default array of KnowledgeWords, mostly punctuation
enum defaultWords = [
	// The start/end of line entry, used as a stopping point when extending a sentence
	KnowledgeWord("", SpecialEffect.SENTENCE_TERMINATOR)
];

// Avoid circular reference (dmd bug?)
// These should be moved inside Knowledge if possible
enum terminator = defaultWords.countUntil!((x,y) => x.special == y)(SpecialEffect.SENTENCE_TERMINATOR);
struct Knowledge {
	private KnowledgeWord[] words = defaultWords;
	private size_t[string] wordMap;
	public alias terminator = .terminator;

	auto find(const string word) const @safe pure
	out(result; result.isNull || result.get() <= words.length)
	{
		import std.typecons : nullable;
		if (auto foundWord = word in wordMap) {
			return nullable(*foundWord);
		}

		return typeof(return).init;
	}

	private size_t learnWord(const string word, size_t factor = 1) @safe pure {
		import std.range : front;

		const index = wordMap.require(word, words.length);
		if (index == words.length) {
			debug(learning) tracef("Learned word {'%s', id: %u, rank: %u}", word, words.length, index);
			words ~= KnowledgeWord(word, word.front.specialEffect);
		}

		words[index].occurrences += factor;

		debug(learning) tracef("Increased occurrences for word {'%s', occurrences: %s}", word, words[index].occurrences);
		return index;
	}
	void learnString(const string str, size_t factor = 1) @safe pure {
		assimilate(parse(str), factor);
	}

	void assimilate(const string[] strings, size_t factor = 1) @safe pure {
		void addWordOccurrence(const SentenceSequence sequence) @safe {
			static void addSequence(ref KnowledgeLink link, const size_t targetWord, size_t factor) @safe {
				foreach (i, target; link.targets) {
					if (target == targetWord) {
						link.targetsOccurrences[i] += factor;
						return;
					}
				}

				link.targets ~= targetWord;
				link.targetsOccurrences ~= factor;
			}
			addSequence(words[sequence.startPoint].forwardLinks.learn(KnowledgeLinkSequence(sequence.secondHalf[0 .. $-1])), sequence.secondHalf[$-1], factor);
			addSequence(words[sequence.startPoint].backwardLinks.learn(KnowledgeLinkSequence(sequence.firstHalf[1 .. $])), sequence.firstHalf[0], factor);
		}

		debug(learning) trace("Learning phrase ", strings);

		if (strings.length == 0) {
			return;
		}

		auto sequence = initSequence(strings);

		addWordOccurrence(sequence);

		foreach (i; 0..strings.length + SentenceSequence.MarkovOrder + 1) {
			const isValidWord = SentenceSequence.MarkovOrder + i < strings.length;
			const size_t newWordID = isValidWord ? learnWord(strings[SentenceSequence.MarkovOrder + i], factor) : terminator;

			sequence.pushLeft(newWordID);

			addWordOccurrence(sequence);
		}
	}

	auto initSequence(const string[] strings) @safe pure {
		SentenceSequence sequence;

		foreach (i, ref word; sequence[SentenceSequence.MarkovOrder + 1..$]) {
			const validWord = i < strings.length;
			word = validWord ? learnWord(strings[i]) : terminator;
		}
		return sequence;
	}
	auto opIndex(size_t i) const @safe pure {
		return words[i];
	}
	auto pickRandom() const @safe
	in(words.length > 0)
	{
		import std.algorithm.iteration : filter;
		import std.random : randomCover;
		import std.range : iota;
		return iota(0, words.length - 1).randomCover().filter!(x => x != terminator).front;
	}
	void optimize() /*@safe*/ pure {
		foreach (ref word; words) {
			word.forwardLinks.optimize();
			word.backwardLinks.optimize();
		}
		wordMap.rehash();
	}
}
@safe pure unittest {
	import std.algorithm.iteration : map;
	import std.range : enumerate, iota;
	enum words = iota(0, SentenceSequence.MarkovOrder).map!(x => x.text);
	Knowledge k;
	const str = parse(format!"%-(%s %)"(words));
	const seq = k.initSequence(str);
	foreach (word; seq.firstHalf) {
		assert(word == Knowledge.terminator);
	}
	size_t[6] w;
	foreach (idx, word; words.enumerate) {
		w[idx] = k.find(word).get;
	}
	assert(seq.secondHalf == w[0 .. SentenceSequence.MarkovOrder]);
}
@safe pure unittest {
	Knowledge k;
	k.assimilate([]);
}

@safe pure unittest {
	import std.exception : assertThrown;
	import std.algorithm.sorting : isSorted;
	import std.range : indexed;
	Knowledge knowledge;
	assert(knowledge.words[Knowledge.terminator].word == "");
	knowledge.learnString("hello");
	with (knowledge[knowledge.find("hello").get]) {
		assert(word == "hello");
		assert(occurrences == 1);
	}
	knowledge.learnString("word");
	knowledge.learnString("hello");
	with (knowledge[knowledge.find("hello").get]) {
		assert(word == "hello");
		assert(occurrences == 2);
	}

	assert(knowledge.find("hellp").isNull);
}


string[] parse(string input) @safe pure {
	import std.algorithm : canFind;
	import std.array : front;
	import std.uni : isPunctuation, isWhite, toLower;
	import std.utf : codeLength;
	string[] output;
	size_t last;
	for (int i; i < input.length; i++) {
		const chr = input[i..$].front;
		const size = chr.codeLength!char;
		const isWhitespace = chr.isWhite;
		if (isWhitespace || chr.isPunctuation) {
			if (i > last) {
				output ~= input[last..i].toLower();
			}
			if (!isWhitespace) {
				output ~= input[i..i+size];
			}
			last = i+size;
		}
		i += size-1;
	}
	if (last < input.length && !input[last..$].front.isWhite) {
		output ~= input[last..$].toLower();
	}
	return output;
}
@safe pure unittest {
	import std.algorithm.searching : canFind;
	assert(parse("") == []);
	assert(parse("test 1 2 3") == ["test", "1", "2", "3"]);
	assert(parse("7, 8, 9") == ["7", ",", "8", ",", "9"]);
	assert(parse("HELLO WORLD") == ["hello", "world"]);
	assert(parse("                   yeah                        ") == ["yeah"]);
	assert(parse("a") == ["a"]);
}
