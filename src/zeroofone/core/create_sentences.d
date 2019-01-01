module zeroofone.core.create_sentences;

import core.stdc.string;
import std.algorithm;
import std.random;
import std.string;
import std.uni;
import std.experimental.logger;

import zeroofone.core.sequence;
import zeroofone.core.knowledge;
import zeroofone.tool.strings;
import zeroofone.pervasive;

/** Functions to create sentences using a ZoO_knowledge structure *************/

/*
 * Returns the index of a element in {links} chosen randomly according
 * to the distribution in {links_occurrences}.
 * Pre:
 *    (!= occurrences 0).
 *    (== (length links_occurrences) (length links)).
 *    (== (sum links_occurrences) occurrences).
 *    (can_store ZoO_index (length links)).
 */
size_t pick_index(const size_t[] links_occurrences) @safe {
	size_t result, accumulator, random_number;

	result = 0;

	/*
	* Safe:
	* (> (length links_occurrences) 0).
	*/
	accumulator = links_occurrences[0];

	random_number = uniform(0, links_occurrences.length);

	while (accumulator < random_number) {
		/*
		* Safe:
		* (->
		*    (and
		*       (== accumulator (sum links_occurrences[0:result]))
		*       (< accumulator random_number)
		*       (< random_number occurrences)
		*       (== occurrences (sum links_occurrences))
		*       (can_store ZoO_index (length links))
		*       (== (length links_occurrences) (length links))
		*    )
		*    (and
		*       (< result' (length links_occurrences))
		*       (can_store ZoO_index result')
		*       (=< accumulator' occurrences)
		*    )
		* )
*/
		result += 1;
		accumulator += links_occurrences[result];
	}

	/* Safe: (< result (length links)) */
	return result;
}

string extend_left(ref ZoO_knowledge k, size_t[ZoO_MARKOV_ORDER] sequence, ref string current_sentence, ref size_t credits) @safe {
	string next_sentence;
	size_t j;

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
			default:
				assert(0);
		}

		current_sentence = next_sentence;

		sequence = 0~sequence[0..$-1];

		if (ZoO_knowledge_find_link(w.backward_links, sequence[1..$], j) < 0) {
			error("Unexpectedly, no backtracking link was found.");

			break;
		}

		sequence[0] = w.backward_links[j].targets[pick_index(w.backward_links[j].targets_occurrences)];

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
	k.find("hello", seq[0]);
	k.find("world", seq[1]);
	k.find("3", seq[2]);
	assert(extend_left(k, seq, str, credits) == " hello world 3");
}

string extend_right(ref ZoO_knowledge k, size_t[ZoO_MARKOV_ORDER] sequence, ref string current_sentence, ref size_t credits) @safe {
	string next_sentence;
	size_t j;

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
			default:
				assert(0);
		}

		current_sentence = next_sentence;

		sequence = sequence[1..$]~0;

		if (ZoO_knowledge_find_link(w.forward_links, sequence, j) < 0) {
			error("Unexpectedly, no forward link was found.");

			break;
		}

		sequence[ZoO_MARKOV_ORDER - 1] = w.forward_links[j].targets[pick_index(w.forward_links[j].targets_occurrences)];
	}
	assert(0);
}

@safe unittest {
	ZoO_knowledge k;
	string str;
	size_t credits = 3;
	k.learnString("hello world 3");
	size_t[3] seq;
	k.find("hello", seq[0]);
	k.find("world", seq[1]);
	k.find("3", seq[2]);
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
	size_t i, j, accumulator, random_number;
	ZoO_knowledge_word * fiw;

	sequence[ZoO_MARKOV_ORDER] = select_first_word(k, string, aliases, randomStart);

	fiw = &k.words[sequence[ZoO_MARKOV_ORDER]];

	for (i = 0; i < ZoO_MARKOV_ORDER; ++i) {
		sequence[ZoO_MARKOV_ORDER - i - 1] = ZoO_WORD_START_OF_LINE;
		sequence[ZoO_MARKOV_ORDER + i + 1] = ZoO_WORD_END_OF_LINE;
	}

	if (fiw.forward_links.length == 0) {
		critical("First word has no forward links.");

		return;
	}

	/* Chooses a likely forward link for the pillar. */
	i = 0;
	accumulator = fiw.forward_links[0].targets_occurrences.length;

	random_number = uniform(0, fiw.occurrences);

	while (accumulator < random_number) {
		accumulator += fiw.forward_links[i].targets_occurrences.length;
		i += 1;
	}

/*   i = uniform(0, cast(ZoO_index)fiw.forward_links.length); */

	/* Copies the forward link data into the sequence. */
	/* This adds (ZoO_MARKOV_ORDER - 1) words, as the ZoO_MARKOV_ORDERth word */
	/* is chosen aftewards. */
	fiw.forward_links[i].sequence = sequence[ZoO_MARKOV_ORDER+1];

	/* selects the last word */
	sequence[ZoO_MARKOV_ORDER * 2] = fiw.forward_links[i].targets[pick_index(fiw.forward_links[i].targets_occurrences)];

	/* FIXME: Not clear enough. */
	/* Now that we have the right side of the sequence, we are going to */
	/* build the left one, one word at a time. */
	for (i = 0; i < ZoO_MARKOV_ORDER; ++i) {
		/* temporary pillar (starts on the right side, minus one so we don't */
		fiw = &k.words[sequence[(ZoO_MARKOV_ORDER * 2) - i - 1]];

		/* finds the backward link corresponding to the words left of the */
		/* temporary pillar. */
		if (ZoO_knowledge_find_link(fiw.backward_links, sequence[ZoO_MARKOV_ORDER - i..$], j) < 0) {
			errorf("Unexpectedly, no back link was found at i=%u, expected to find a backlink with %s, from %s.", i, k.words[sequence[(ZoO_MARKOV_ORDER - i)]].word, fiw.word);
			error("Sequence was:");

			for (j = 0; j <= (ZoO_MARKOV_ORDER * 2); ++j) {
				errorf("[%u] %s", j, k.words[sequence[j]].word);
			}

			break;
		}

		sequence[ZoO_MARKOV_ORDER - i - 1] = fiw.backward_links[j].targets[pick_index(fiw.backward_links[j].targets_occurrences)];
	}
}
string ZoO_knowledge_extend(ref ZoO_knowledge k, const ZoO_strings str, const string[] aliases, bool randomStart) @safe
out(result; result.length > 0)
out(result; !isWhite(result[0]))
out(result; !isWhite(result[$-1]))
{
	string result;
	int word_found;
	size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence;
	size_t credits;
	size_t first_word;

	credits = ZoO_MAX_REPLY_WORDS;

	init_sequence(k, str, aliases, sequence, randomStart);

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

	debug(create) tracef("full sequence: sequence: %s (%s), start of sentence: %s", sequence, sequence[].map!(x => k.words[x].word), result);

	result = extend_right(k, sequence[ZoO_MARKOV_ORDER + 1..$], result, credits);

	result = extend_left(k, sequence[0..ZoO_MARKOV_ORDER], result, credits);

	return result.strip();
}
