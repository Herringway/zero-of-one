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
import zeroofone.tool.strings;

/// Create sentences based on existing Knowledge

auto extendLeft(const Knowledge k, HalfSentenceSequence sequence) @safe {
	size_t[] sentence;
	while (k[sequence[$-1]].special != SpecialEffect.SENTENCE_TERMINATOR) {
		sentence = sequence[$ - 1] ~ sentence;

		const w = k[sequence[$ - 1]];
		debug(create) tracef("Current word: %s - %s", w.word, w.special);

		sequence = 0~sequence[0..$-1];

		auto found = w.backwardLinks.find!((x,y) => x.sequence == y)(sequence[1..$]);
		assert(!found.empty, "Unexpectedly, no backtracking link was found.");

		sequence[0] = found.front.targets[dice(found.front.targetsOccurrences)];
	}
	return sentence;
}

@safe unittest {
	Knowledge k;
	k.assimilate(Strings(["hello", "world", "3"]));
	HalfSentenceSequence seq;
	assert(k.find("hello", seq[0]));
	assert(k.find("world", seq[1]));
	assert(k.find("3", seq[2]));
	assert(extendLeft(k, seq).equal(only(seq[0], seq[1], seq[2])));
}

auto extendRight(const Knowledge k, HalfSentenceSequence sequence) @safe pure @nogc {
	static struct Result {
		HalfSentenceSequence chain;
		const Knowledge knowledge;
		bool empty() const @safe pure {
			return knowledge[front].special == SpecialEffect.SENTENCE_TERMINATOR;
		}
		auto front() const @safe pure {
			return chain[0];
		}
		void popFront() @safe {
			const w = knowledge[front];
			debug(create) tracef("Current word: %s - %s", w.word, w.special);

			chain = chain[1..$] ~ 0;

			auto found = w.forwardLinks.find!((x,y) => x.sequence == y)(chain[0..$-1]);
			assert(!found.empty, "Unexpectedly, no forward link was found.");

			chain[$ - 1] = found.front.targets[dice(found.front.targetsOccurrences)];
		}
	}
	return Result(sequence, k);
}

@safe /+pure @nogc+/ unittest {
	Knowledge k;
	k.learnString("hello world 3");
	HalfSentenceSequence seq;
	assert(k.find("hello", seq[0]));
	assert(k.find("world", seq[1]));
	assert(k.find("3", seq[2]));
	assert(extendRight(k, seq).equal(only(seq[0], seq[1], seq[2])));
}

size_t selectFirstWord(const Knowledge k, const Strings string, const bool useRandomWord) @safe {
	size_t wordMinScore;
	bool wordFound;

	if (useRandomWord) {
		return uniform(0, k.length);
	}

	wordFound = false;

	size_t wordMinID;
	foreach (word; string.words) {
		if (k.find(word, wordMinID)) {
			wordFound = true;
			wordMinScore = k[wordMinID].occurrences;

			break;
		}
	}

	if (!wordFound) {
		return uniform(0, k.length);
	}

	size_t wordID;
	foreach (word; string.words) {
		if (k.find(word, wordID) && (k[wordID].occurrences < wordMinScore)) {
			wordMinScore = k[wordID].occurrences;
			wordMinID = wordID;
		}
	}

	return wordMinID;
}


auto newSequence(const Knowledge k, const Strings string, const bool randomStart) @safe {
	SentenceSequence sequence;

	sequence[SentenceSequence.MarkovOrder] = selectFirstWord(k, string, randomStart);

	const anchor = k[sequence.startPoint];

	assert(anchor.forwardLinks.length > 0, "First word has no forward links.");

	/* Chooses a likely forward link for the pillar. */

	const selectedLinks = anchor.forwardLinks[uniform(0, anchor.forwardLinks.length)];

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
		const found = fiw.backwardLinks.find!((x,y) => x.sequence == y)(link);
		assert(!found.empty, format!"No back link found for %s"(link));

		sequence[SentenceSequence.MarkovOrder - i - 1] = found.front.targets[dice(found.front.targetsOccurrences)];
	}
	return sequence;
}
string knowledgeExtend(const Knowledge k, const Strings str, const bool randomStart) @safe
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

	string result;
	// Start with something that'll capitalize the first word
	SpecialEffect lastEffect = SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD;
	foreach (const word; chain(leftSide, only(sequence.startPoint), rightSide).map!(x => k[x])) {
		result ~= format!"%s%s"(word.special.useTrailingSpace ? " " : "", autoCapitalize(word.word, lastEffect.capitalizesNext));
		lastEffect = word.special;
	}

	return result.strip();
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
