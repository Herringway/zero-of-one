module zeroofone.core.create_sentences;

import core.stdc.string;
import std.algorithm;
import std.array;
import std.random;
import std.string;
import std.uni;
import std.experimental.logger;

import zeroofone.core.sequence;
import zeroofone.core.knowledge;
import zeroofone.tool.strings;
import zeroofone.pervasive;

/** Functions to create sentences using a ZoO_knowledge structure *************/

string extend_left(ref ZoO_knowledge k, size_t[ZoO_MARKOV_ORDER] sequence, ref string current_sentence, ref size_t credits) @safe {
	string next_sentence;

	next_sentence = current_sentence;
	debug(create) tracef("extend-left: sequence: %s (%s), credits: %s, sentence: %s", sequence, sequence[].map!(x => k.words[x].word), credits, current_sentence);

	for (;;) {
		if (credits == 0) {
			return current_sentence;
		}

		credits -= 1;

		const w = k.words[sequence[ZoO_MARKOV_ORDER - 1]];

		next_sentence = current_sentence;

		switch(w.special) {
			case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
				next_sentence = format!" %s%s"(w.word, current_sentence);
				break;
			case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
				next_sentence = format!"%s%s"(w.word, current_sentence);
				break;
			case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
				next_sentence = format!"%s%s"(w.word, current_sentence[1..$]);
				break;
			case ZoO_knowledge_special_effect.STARTS_SENTENCE:
				return current_sentence;
			default:
				assert(0);
		}

		current_sentence = next_sentence;

		sequence = 0~sequence[0..$-1];

		auto found = w.backward_links.find!((x,y) => x.sequence == y)(sequence[1..$]);
		assert(!found.empty, "Unexpectedly, no backtracking link was found.");

		sequence[0] = found.front.targets[dice(found.front.targets_occurrences)];

		/* prevents current_sentence [const] */
		current_sentence = next_sentence;
	}
	assert(0);
}

@safe unittest {
	ZoO_knowledge k;
	string str;
	size_t credits = 3;
	k.learnString("hello world 3");
	size_t[3] seq;
	assert(k.find("hello", seq[0]));
	assert(k.find("world", seq[1]));
	assert(k.find("3", seq[2]));
	assert(extend_left(k, seq, str, credits) == " hello world 3");
}

string extend_right(ref ZoO_knowledge k, size_t[ZoO_MARKOV_ORDER] sequence, ref string current_sentence, ref size_t credits) @safe {
	string next_sentence;

	next_sentence = current_sentence;
	debug(create) tracef("extend-right: sequence: %s (%s), credits: %s, sentence: %s", sequence, sequence[].map!(x => k.words[x].word), credits, current_sentence);

	for (;;) {
		if (credits == 0) {
			return current_sentence;
		}

		credits -= 1;

		const w = k.words[sequence[0]];

		next_sentence = current_sentence;

		switch (w.special) {
			case ZoO_knowledge_special_effect.HAS_NO_EFFECT, ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
				next_sentence = format!"%s%s "(current_sentence, w.word);
				break;
			case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
				next_sentence = format!"%s%s"(current_sentence, w.word);
				break;
			case ZoO_knowledge_special_effect.ENDS_SENTENCE:
				return current_sentence;
			default:
				assert(0);
		}

		current_sentence = next_sentence;

		sequence = sequence[1..$]~0;

		auto found = w.forward_links.find!((x,y) => x.sequence == y)(sequence[0..$-1]);
		assert(!found.empty, "Unexpectedly, no forward link was found.");

		sequence[ZoO_MARKOV_ORDER - 1] = found.front.targets[dice(found.front.targets_occurrences)];
	}
	assert(0);
}

@safe unittest {
	ZoO_knowledge k;
	string str;
	size_t credits = 3;
	k.learnString("hello world 3");
	size_t[3] seq;
	assert(k.find("hello", seq[0]));
	assert(k.find("world", seq[1]));
	assert(k.find("3", seq[2]));
	auto result = extend_right(k, seq, str, credits);
	assert(result == "hello world 3 ");
}

size_t select_first_word(ref ZoO_knowledge k, const ZoO_strings string, const string[] aliases, const bool useRandomWord) @safe {
	import std.algorithm.searching : canFind;
	size_t i, word_min_score, word_id, word_min_id;
	bool word_found;

	if (useRandomWord) {
		return uniform(0, k.words.length);
	}

	word_found = false;

	for (i = 0; i < string.words.length; ++i) {
		if (aliases.canFind(string.words[i])) {
			continue;
		}

		if (k.find(string.words[i], word_min_id) == 0) {
			word_found = true;
			word_min_score = k.words[word_min_id].occurrences;

			break;
		}
	}

	if (!word_found) {
		return uniform(0, k.words.length);
	}

	for (; i < string.words.length; ++i) {
		if (aliases.canFind(string.words[i])) {
			continue;
		}

		if ((k.find(string.words[i], word_id) == 0) && (k.words[word_id].occurrences < word_min_score)) {
			word_min_score = k.words[word_id].occurrences;
			word_min_id = word_id;
		}
	}

	return word_min_id;
}


void init_sequence(ref ZoO_knowledge k, const ZoO_strings string, const string[] aliases, ref size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence, bool randomStart) @safe {
	import std.conv : text;
	ZoO_knowledge_word fiw;

	sequence[ZoO_MARKOV_ORDER] = select_first_word(k, string, aliases, randomStart);

	fiw = k.words[sequence[ZoO_MARKOV_ORDER]];

	sequence[0..ZoO_MARKOV_ORDER] = ZoO_WORD_START_OF_LINE;
	sequence[ZoO_MARKOV_ORDER+1..$] = ZoO_WORD_END_OF_LINE;

	if (fiw.forward_links.length == 0) {
		critical("First word has no forward links.");

		return;
	}

	/* Chooses a likely forward link for the pillar. */

	auto selectedLinks = choice(fiw.forward_links);

	/* Copies the forward link data into the sequence. */
	/* This adds (ZoO_MARKOV_ORDER - 1) words, as the ZoO_MARKOV_ORDERth word */
	/* is chosen aftewards. */
	sequence[ZoO_MARKOV_ORDER + 1..ZoO_MARKOV_ORDER + 3] = selectedLinks.sequence;

	/* selects the last word */
	sequence[ZoO_MARKOV_ORDER * 2] = selectedLinks.targets[dice(selectedLinks.targets_occurrences)];

	/* FIXME: Not clear enough. */
	/* Now that we have the right side of the sequence, we are going to */
	/* build the left one, one word at a time. */
	foreach (i; 0..ZoO_MARKOV_ORDER) {
		/* temporary pillar (starts on the right side, minus one so we don't */
		fiw = k.words[sequence[(ZoO_MARKOV_ORDER * 2) - i - 1]];

		/* finds the backward link corresponding to the words left of the */
		/* temporary pillar. */
		auto found = fiw.backward_links.find!((x,y) => x.sequence == y)(sequence[ZoO_MARKOV_ORDER - i..ZoO_MARKOV_ORDER - i + ZoO_SEQUENCE_SIZE]);
		if (found.empty) {
			errorf("Unexpectedly, no back link was found at i=%u, expected to find a backlink with %s, from %s.", i, k.words[sequence[(ZoO_MARKOV_ORDER - i)]].word, fiw.word);
			errorf("Sequence was: [%(%u, %)] -> %-(%s %)", sequence, sequence[].map!(x => k.words[x].word));

			break;
		}

		sequence[ZoO_MARKOV_ORDER - i - 1] = found.front.targets[dice(found.front.targets_occurrences)];
	}
}
string ZoO_knowledge_extend(ref ZoO_knowledge k, const ZoO_strings str, const string[] aliases, bool randomStart) @safe
out(result; result.length > 0)
out(result; !isWhite(result[0]))
out(result; !isWhite(result[$-1]))
{
	string result;
	size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence;
	size_t credits;
	size_t first_word;

	credits = ZoO_MAX_REPLY_WORDS;

	init_sequence(k, str, aliases, sequence, randomStart);

	debug(create) tracef("initial sequence: sequence: %s (%s)", sequence, sequence[].map!(x => k.words[x].word));

	first_word = sequence[ZoO_MARKOV_ORDER];

	switch (k.words[first_word].special) {
		case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
			result = format!"%s "(k.words[first_word].word);
			break;

		case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
			result = format!" %s"(k.words[first_word].word);
			break;

		case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
			result = format!" %s "(k.words[first_word].word);
			break;

		default:
			warningf("'%s' was unexpectedly selected as pillar.", k.words[first_word].word);
			result = format!" [%s] "(k.words[first_word].word);
			break;
	}

	debug(create) tracef("start of sentence: %s", result);

	result = extend_right(k, sequence[ZoO_MARKOV_ORDER + 1..$], result, credits);

	result = extend_left(k, sequence[0..ZoO_MARKOV_ORDER], result, credits);

	return result.strip();
}
