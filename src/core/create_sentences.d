module core.create_sentences;

import core.stdc.string;
import std.random;
import std.string;
import std.experimental.logger;

import core.sequence;
import core.knowledge;
import io.error;
import tool.strings;
import pervasive;

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
ZoO_index pick_index(const ZoO_index[] links_occurrences) @safe {
	ZoO_index result, accumulator, random_number;

	result = 0;

	/*
	* Safe:
	* (> (length links_occurrences) 0).
	*/
	accumulator = links_occurrences[0];

	random_number = uniform(0, cast(uint)links_occurrences.length);

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

char[] extend_left(ref ZoO_knowledge k, ZoO_index[] sequence, ZoO_char[] current_sentence, ref ZoO_index credits) {
	size_t addition_size;
	ZoO_knowledge_word * w;
	ZoO_char[] next_sentence;
	ZoO_index j;

	next_sentence = current_sentence;

	for (;;) {
		if (credits == 0) {
			return current_sentence;
		}

		credits -= 1;

		w = &k.words[sequence[ZoO_MARKOV_ORDER - 1]];

		switch (w.special) {
			case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
				/* FIXME: not overflow-safe. */
				/* word also contains an '\0', which we will replace by a ' ' */
				addition_size = w.word_size;
				break;

			case ZoO_knowledge_special_effect.ENDS_SENTENCE:
				warning("END OF LINE should not be prefixable.");
				return current_sentence;

			case ZoO_knowledge_special_effect.STARTS_SENTENCE:
				return current_sentence;

			case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
			case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
				/* word also contains an '\0', which we will remove. */
				addition_size = w.word_size - 1;
				break;
			default: assert(0);
		}

		if (current_sentence.length > (size_t.max - addition_size)) {
			warning("Sentence construction aborted to avoid size_t overflow.");

			return current_sentence;
		}

		next_sentence = current_sentence;

		/* overflow-safe */
		next_sentence.length = (current_sentence.length + addition_size);
		current_sentence.length = (current_sentence.length + addition_size);

		switch(w.special) {
			case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
				next_sentence = format!" %s%s"(w.word, current_sentence).dup;
				break;

			case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
				next_sentence = format!"%s%s"(w.word, current_sentence).dup;
				break;

			case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
				next_sentence = format!"%s%s"(w.word, current_sentence[1..$]).dup;
				break;

			default:
				/* TODO: PROGRAM LOGIC ERROR */
				break;
		}

		/* prevents current_sentence [const] */
		current_sentence = next_sentence;

		memmove(&sequence[1], &sequence[0], (ZoO_index.sizeof * (ZoO_MARKOV_ORDER - 1)));

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

char[] extend_right(ref ZoO_knowledge k, ZoO_index[] sequence, ZoO_char[] current_sentence, ref ZoO_index credits) {
	size_t addition_size;
	ZoO_knowledge_word * w;
	ZoO_char[] next_sentence;
	ZoO_index j;

	next_sentence = current_sentence;

	for (;;) {
		if (credits == 0) {
			return current_sentence;
		}

		credits -= 1;

		w = &k.words[sequence[0]];

		switch (w.special) {
			case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
				/* FIXME: Assumed to be overflow-safe. */
				/* word also contains an '\0', which we will replace by a ' '. */
				addition_size = w.word_size;
				break;

			case ZoO_knowledge_special_effect.ENDS_SENTENCE:
				return current_sentence;

			case ZoO_knowledge_special_effect.STARTS_SENTENCE:
				warning("START OF LINE should not be suffixable.");
				return current_sentence;

			case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
			case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
				/* word also contains an '\0', which we will remove. */
				addition_size = w.word_size - 1;
				break;
			default: assert(0);
		}

		if (current_sentence.length > (size_t.max - addition_size)) {
			warning("Sentence construction aborted to avoid size_t overflow.");

			return current_sentence;
		}

		next_sentence = current_sentence;

		next_sentence.length = (current_sentence.length + addition_size);
		current_sentence.length = (current_sentence.length + addition_size);

		switch (w.special) {
			case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
				goto case;

			case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
				next_sentence = format!"%s%s "(current_sentence, w.word).dup;
				break;

			case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
				next_sentence = format!"%s%s"(current_sentence, w.word).dup;
				break;

			default:
				/* TODO: PROGRAM LOGIC ERROR */
				break;
		}

		/* prevents current_sentence [const] */
		current_sentence = next_sentence;

		memmove(sequence.ptr, sequence.ptr + 1, (ZoO_index.sizeof * (ZoO_MARKOV_ORDER - 1)));

		if (ZoO_knowledge_find_link(w.forward_links, sequence, j) < 0) {
			error("Unexpectedly, no forward link was found.");

			break;
		}

		sequence[ZoO_MARKOV_ORDER - 1] = w.forward_links[j].targets[pick_index(w.forward_links[j].targets_occurrences)];
	}
	assert(0);
}

ZoO_index select_first_word(ref ZoO_knowledge k, const ZoO_strings* string, const string[] aliases) {
	ZoO_index i, j, word_id, word_min_score, word_min_id;
	ZoO_index word_found;

	if (string == null) {
		return word_min_id = uniform(0, cast(uint)k.words.length);
	}

	word_found = 0;

	for (i = 0; i < string.words.length; ++i) {
		for (j = 0; j < aliases.length; ++j) {
			if (aliases[j] == string.words[i]) {
				goto NEXT_WORD;
			}
		}

		if (k.find(string.words[i], word_min_id) == 0) {
			word_found = 1;
			word_min_score = k.words[word_min_id].occurrences;

			break;
		}

		NEXT_WORD:;
	}

	if (word_found == 0) {
		return word_min_id = uniform(0, cast(uint)k.words.length);
	}

	for (; i < string.words.length; ++i) {
		for (j = 0; j < aliases.length; ++j) {
			if (aliases[j] == string.words[i]) {
				goto NEXT_WORD_BIS;
			}
		}

		if ((k.find(string.words[i], word_id) == 0) && (k.words[word_id].occurrences < word_min_score)) {
			word_min_score = k.words[word_id].occurrences;
			word_min_id = word_id;
		}

		NEXT_WORD_BIS:;
	}

	return word_min_id;
}


void init_sequence(ref ZoO_knowledge k, const ZoO_strings* string, const string[] aliases, ref ZoO_index[(ZoO_MARKOV_ORDER * 2) + 1] sequence) {
	import std.conv : text;
	ZoO_index i, j, accumulator, random_number;
	ZoO_knowledge_word * fiw;

	sequence[ZoO_MARKOV_ORDER] = select_first_word(k, string, aliases);

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
	accumulator = cast(uint)fiw.forward_links[0].targets_occurrences.length;

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
int ZoO_knowledge_extend(ref ZoO_knowledge k, const ZoO_strings* string, const string[] aliases, out ZoO_char[] result) {
	int word_found;
	size_t sentence_size;
	ZoO_index[(ZoO_MARKOV_ORDER * 2) + 1] sequence;
	ZoO_index first_word, credits;

	credits = ZoO_MAX_REPLY_WORDS;

	init_sequence(k, string, aliases, sequence);

	first_word = sequence[ZoO_MARKOV_ORDER];

	switch (k.words[first_word].special) {
		case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
		case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
			sentence_size = k.words[first_word].word.length + 2;
			break;

		case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
			sentence_size = k.words[first_word].word.length + 3;
			break;

		default:
			warningf("'%s' was unexpectedly selected as pillar.", k.words[first_word].word);
			sentence_size = k.words[first_word].word.length + 5;
			break;
	}

	result = new ZoO_char[](sentence_size);

	switch (k.words[first_word].special) {
		case ZoO_knowledge_special_effect.REMOVES_LEFT_SPACE:
			result = format!"%s "(k.words[first_word].word).dup;
			break;

		case ZoO_knowledge_special_effect.REMOVES_RIGHT_SPACE:
			result = format!" %s"(k.words[first_word].word).dup;
			break;

		case ZoO_knowledge_special_effect.HAS_NO_EFFECT:
			result = format!" %s "(k.words[first_word].word).dup;
			break;

		default:
			result = format!" [%s] "(k.words[first_word].word).dup;
			break;
	}

	result = extend_right(k, sequence[ZoO_MARKOV_ORDER + 1..$], result, credits);

	result = extend_left(k, sequence, result, credits);

	return 0;
}