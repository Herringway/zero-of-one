module zeroofone.core.create_sentences;

import std.algorithm;
import std.array;
import std.random;
import std.string;
import std.uni;
import std.experimental.logger;

import zeroofone.core.sequence;
import zeroofone.core.knowledge;
import zeroofone.tool.strings;

/// Create sentences based on existing Knowledge

string extendLeft(const Knowledge k, HalfSentenceSequence sequence, ref string currentSentence) @safe {
	auto nextSentence = currentSentence;
	debug(create) tracef("extendLeft: sequence: %s (%s), sentence: %s", sequence, sequence[].map!(x => k.words[x].word), currentSentence);

	while (true) {
		const w = k.words[sequence[$ - 1]];

		nextSentence = currentSentence;

		final switch(w.special) {
			case SpecialEffect.HAS_NO_EFFECT:
				nextSentence = format!" %s%s"(w.word, currentSentence);
				break;
			case SpecialEffect.REMOVES_LEFT_SPACE:
				nextSentence = format!"%s%s"(w.word, currentSentence);
				break;
			case SpecialEffect.REMOVES_RIGHT_SPACE:
				nextSentence = format!"%s%s"(w.word, currentSentence[1..$]);
				break;
			case SpecialEffect.STARTS_SENTENCE:
				return currentSentence;
			case SpecialEffect.ENDS_SENTENCE:
				assert(0);
		}

		currentSentence = nextSentence;

		sequence = 0~sequence[0..$-1];

		auto found = w.backwardLinks.find!((x,y) => x.sequence == y)(sequence[1..$]);
		assert(!found.empty, "Unexpectedly, no backtracking link was found.");

		sequence[0] = found.front.targets[dice(found.front.targetsOccurrences)];

		/* prevents currentSentence [const] */
		currentSentence = nextSentence;
	}
}

@safe unittest {
	Knowledge k;
	string str;
	k.learnString("hello world 3");
	HalfSentenceSequence seq;
	assert(k.find("hello", seq[0]));
	assert(k.find("world", seq[1]));
	assert(k.find("3", seq[2]));
	assert(extendLeft(k, seq, str) == " hello world 3");
}

string extendRight(const Knowledge k, HalfSentenceSequence sequence, ref string currentSentence) @safe {
	auto nextSentence = currentSentence;
	debug(create) tracef("extendRight: sequence: %s (%s), sentence: %s", sequence, sequence[].map!(x => k.words[x].word), currentSentence);

	while (true) {
		const w = k.words[sequence[0]];

		nextSentence = currentSentence;

		final switch (w.special) {
			case SpecialEffect.HAS_NO_EFFECT:
			case SpecialEffect.REMOVES_LEFT_SPACE:
				nextSentence = format!"%s%s "(currentSentence, w.word);
				break;
			case SpecialEffect.REMOVES_RIGHT_SPACE:
				nextSentence = format!"%s%s"(currentSentence, w.word);
				break;
			case SpecialEffect.ENDS_SENTENCE:
				return currentSentence;
			case SpecialEffect.STARTS_SENTENCE:
				assert(0);
		}

		currentSentence = nextSentence;

		sequence = sequence[1..$]~0;

		auto found = w.forwardLinks.find!((x,y) => x.sequence == y)(sequence[0..$-1]);
		assert(!found.empty, "Unexpectedly, no forward link was found.");

		sequence[$ - 1] = found.front.targets[dice(found.front.targetsOccurrences)];
	}
}

@safe unittest {
	Knowledge k;
	string str;
	k.learnString("hello world 3");
	HalfSentenceSequence seq;
	assert(k.find("hello", seq[0]));
	assert(k.find("world", seq[1]));
	assert(k.find("3", seq[2]));
	auto result = extendRight(k, seq, str);
	assert(result == "hello world 3 ");
}

size_t selectFirstWord(const Knowledge k, const Strings string, const bool useRandomWord) @safe {
	size_t wordMinScore;
	bool wordFound;

	if (useRandomWord) {
		return uniform(0, k.words.length);
	}

	wordFound = false;

	size_t wordMinID;
	foreach (word; string.words) {
		if (k.find(word, wordMinID)) {
			wordFound = true;
			wordMinScore = k.words[wordMinID].occurrences;

			break;
		}
	}

	if (!wordFound) {
		return uniform(0, k.words.length);
	}

	size_t wordID;
	foreach (word; string.words) {
		if (k.find(word, wordID) && (k.words[wordID].occurrences < wordMinScore)) {
			wordMinScore = k.words[wordID].occurrences;
			wordMinID = wordID;
		}
	}

	return wordMinID;
}


auto newSequence(const Knowledge k, const Strings string, const bool randomStart) @safe {
	SentenceSequence sequence;

	sequence[SentenceSequence.MarkovOrder] = selectFirstWord(k, string, randomStart);

	const anchor = k.words[sequence.startPoint];

	sequence[0..SentenceSequence.MarkovOrder] = Knowledge.startOfLine;
	sequence[SentenceSequence.MarkovOrder+1..$] = Knowledge.endOfLine;

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
		const fiw = k.words[sequence[$ - i - 2]];

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
	const sequence = newSequence(k, str, randomStart);

	debug(create) tracef("initial sequence: sequence: %s (%s)", sequence, sequence[].map!(x => k.words[x].word));

	const firstWord = sequence.startPoint;

	string result;
	final switch (k.words[firstWord].special) {
		case SpecialEffect.REMOVES_LEFT_SPACE:
			result = format!"%s "(k.words[firstWord].word);
			break;
		case SpecialEffect.REMOVES_RIGHT_SPACE:
			result = format!" %s"(k.words[firstWord].word);
			break;
		case SpecialEffect.HAS_NO_EFFECT:
			result = format!" %s "(k.words[firstWord].word);
			break;
		case SpecialEffect.STARTS_SENTENCE:
		case SpecialEffect.ENDS_SENTENCE:
			assert(0, "START OF LINE or END OF LINE was unexpectedly selected as pillar.");
	}

	debug(create) tracef("start of sentence: %s", result);

	result = extendRight(k, sequence.secondHalf, result);

	result = extendLeft(k, sequence.firstHalf, result);

	return result.strip();
}
