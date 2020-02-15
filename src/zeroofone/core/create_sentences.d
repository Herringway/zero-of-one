module zeroofone.core.create_sentences;

import std.algorithm;
import std.array;
import std.random;
import std.range;
import std.string;
import std.uni;
import std.experimental.logger;

import zeroofone.core.sequence;
import zeroofone.core.knowledge;

/// Create sentences based on existing Knowledge

auto extendLeft(const Knowledge k, HalfSentenceSequence sequence) @safe {
	size_t[] sentence;
	while (!k[sequence[$-1]].isTerminator) {
		sentence = sequence[$ - 1] ~ sentence;

		const w = k[sequence[$ - 1]];
		debug(create) tracef("Current word: %s - %s", w.word, w.special);

		sequence.pushRight(0);

		auto found = w.backwardLinks.findSequence(sequence.asKnowledgeLinkSequenceLeft);
		assert(!found.isNull, "Unexpectedly, no backtracking link was found.");

		sequence[0] = found.get.targets[dice(found.get.targetsOccurrences)];
	}
	return sentence;
}

@safe unittest {
	Knowledge k;
	k.assimilate(["hello", "world", "3"]);
	auto seq = HalfSentenceSequence([k.findNew("hello").get, k.findNew("world").get, k.findNew("3").get]);
	assert(extendLeft(k, seq).map!(x => k[x].word).equal(only("hello", "world", "3")));
}

auto extendRight(const Knowledge k, HalfSentenceSequence sequence) @safe pure @nogc {
	static struct Result {
		HalfSentenceSequence chain;
		const Knowledge knowledge;
		bool empty() const @safe pure {
			return knowledge[front].isTerminator;
		}
		auto front() const @safe pure {
			return chain[0];
		}
		void popFront() @safe {
			const w = knowledge[front];
			debug(create) tracef("Current word: %s - %s", w.word, w.special);

			chain.pushLeft(0);

			auto found = w.forwardLinks.findSequence(chain.asKnowledgeLinkSequenceRight);
			assert(!found.isNull, "Unexpectedly, no forward link was found.");

			chain[$ - 1] = found.get.targets[dice(found.get.targetsOccurrences)];
		}
	}
	return Result(sequence, k);
}

@safe /+pure @nogc+/ unittest {
	Knowledge k;
	k.learnString("hello world 3");
	auto seq = HalfSentenceSequence([k.findNew("hello").get, k.findNew("world").get, k.findNew("3").get]);
	assert(extendRight(k, seq).map!(x => k[x].word).equal(only("hello", "world", "3")));
}

size_t selectFirstWord(const Knowledge k, const string[] strings) @safe {
	size_t wordMinScore = size_t.max;
	bool wordFound;
	size_t wordMinID;

	// We want the rarest word in the sequence.
	foreach (word; strings) {
		const foundWord = k.findNew(word);
		if (!foundWord.isNull && (k[foundWord.get].occurrences < wordMinScore)) {
			wordFound = true;
			wordMinScore = k[foundWord.get].occurrences;
			wordMinID = foundWord.get;
		}
	}

	if (!wordFound) {
		return k.pickRandom();
	}

	return wordMinID;
}

@safe unittest {
	Knowledge k;
	k.learnString("hello world 3");
	assert(selectFirstWord(k, ["hello"]) == k.findNew("hello").get);
	assert(selectFirstWord(k, ["hellp"]) != Knowledge.terminator);
	assert(selectFirstWord(k, ["hello", "world", "3"]).among(k.findNew("hello").get, k.findNew("world").get, k.findNew("3").get));
}

auto newSequence(const Knowledge k, const string[] strings, const bool randomStart) @safe {
	SentenceSequence sequence;

	// Put the anchor word in the middle of the sequence
	sequence[SentenceSequence.MarkovOrder] = randomStart ? k.pickRandom() : selectFirstWord(k, strings);

	const anchor = k[sequence.startPoint];

	assert(anchor.forwardLinks.length > 0, "First word has no forward links.");

	/* Chooses a likely forward link for the pillar. */

	const selectedLinks = anchor.forwardLinks.randomLink;

	/* Copies the forward link data into the sequence. */
	/* This adds (SentenceSequence.MarkovOrder - 1) words, as the ZoO_SentenceSequence.MarkovOrderth word */
	/* is chosen aftewards. */
	sequence[SentenceSequence.MarkovOrder + 1..SentenceSequence.MarkovOrder + 1 + KnowledgeLinkSequence.Size] = selectedLinks.sequence.sequence;

	/* selects the last word */
	sequence[$ - 1] = selectedLinks.targets[dice(selectedLinks.targetsOccurrences)];

	/* FIXME: Not clear enough. */
	/* Now that we have the right side of the sequence, we are going to */
	/* build the left one, one word at a time. */
	foreach (i; 0..SentenceSequence.MarkovOrder) {
		/* temporary pillar (starts on the right side, minus one so we don't */
		const fiw = k[sequence[$ - i - 2]];

		// finds the backward link corresponding to the words left of the temporary pillar.
		const link = sequence.getKnowledgeLink(-i);
		const found = fiw.backwardLinks.findSequence(link);
		assert(!found.isNull, format!"No back link found for %s"(link));

		sequence[SentenceSequence.MarkovOrder - i - 1] = found.get.targets[dice(found.get.targetsOccurrences)];
	}
	return sequence;
}
string knowledgeExtend(const Knowledge k, const string[] str, const bool randomStart) @safe
out(result; result.length > 0)
out(result; !isWhite(result[0]))
out(result; !isWhite(result[$-1]))
{
	import std.range : chain, only;
	const sequence = newSequence(k, str, randomStart);

	debug(create) tracef("initial sequence: sequence: %s (%s)", sequence, sequence[].map!(x => k[x].word));

	debug(create) tracef("extendRight: sequence: %s (%s)", sequence.secondHalf, sequence.secondHalf[].map!(x => k[x].word));
	auto rightSide = extendRight(k, sequence.secondHalf);

	debug(create) tracef("extendLeft: sequence: %s (%s)", sequence.firstHalf, sequence.firstHalf[].map!(x => k[x].word));
	auto leftSide = extendLeft(k, sequence.firstHalf);
	return createSentence(chain(leftSide, only(sequence.startPoint), rightSide).map!(x => k[x]));
}

string createSentence(T)(T words) {
	string result;
	// Start with something that'll capitalize the first word
	SpecialEffect lastEffect = SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD;
	foreach (const word; words) {
		result ~= format!"%s%s"(word.special.useTrailingSpace ? (lastEffect.hasTrailingSpace ? " " : "") : "", autoCapitalize(word.word, lastEffect.capitalizesNext));
		lastEffect = word.special;
	}

	return result.strip();
}
@safe pure unittest {
	assert(createSentence(KnowledgeWord[].init) == "");
	assert(createSentence([KnowledgeWord(".", SpecialEffect.NO_SPACES)]) == ".");
	assert(createSentence([KnowledgeWord(".", SpecialEffect.REMOVES_LEFT_SPACE)]) == ".");
	assert(createSentence([KnowledgeWord(".", SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD)]) == ".");
	assert(createSentence([KnowledgeWord(".", SpecialEffect.REMOVES_RIGHT_SPACE)]) == ".");
	assert(createSentence([KnowledgeWord(".", SpecialEffect.HAS_NO_EFFECT)]) == ".");
	assert(createSentence([KnowledgeWord("hello"), KnowledgeWord("world"), KnowledgeWord("!", SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD)]) == "Hello world!");
	assert(createSentence([KnowledgeWord("hello"), KnowledgeWord("\"", SpecialEffect.REMOVES_RIGHT_SPACE), KnowledgeWord("world"), KnowledgeWord("\"", SpecialEffect.REMOVES_LEFT_SPACE), KnowledgeWord("!", SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD)]) == "Hello \"world\"!");
}

auto autoCapitalize(const string word, const bool cap) @safe {
	static struct Result {
		const string word;
		const bool capitalize;
		void toString(T)(T sink) const if (isOutputRange!(T, const(char))) {
			if (capitalize) {
				put(sink, word.asCapitalized);
			} else {
				put(sink, word);
			}
		}
	}
	return Result(word, cap);
}
