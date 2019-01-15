module zeroofone.core.assimilate;

import core.stdc.string;
import std.string;
import std.experimental.logger;

import zeroofone.core.knowledge;
import zeroofone.core.sequence;
import zeroofone.pervasive;
import zeroofone.tool.strings;

/** Functions to assimilate sentences using a ZoO_knowledge structure *********/

void add_sequence(ref ZoO_knowledge_link[] links, const size_t[ZoO_MARKOV_ORDER] sequence, const size_t target_i, const size_t offset) @safe {
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
	link.targets[link.targets.length - 1] = sequence[target_i];
	link.targets_occurrences ~= 1;
}

void add_word_occurrence(ref ZoO_knowledge k, const size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence) @safe {
	auto word = &k.words[sequence[ZoO_MARKOV_ORDER]];

	add_sequence(word.forward_links, sequence[ZoO_MARKOV_ORDER + 1..$], (ZoO_MARKOV_ORDER - 1), 0);
	add_sequence(word.backward_links, sequence[0..ZoO_MARKOV_ORDER], 0, 1);
}

void init_sequence(ref ZoO_knowledge k, const ZoO_strings string, ref size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence) @safe {
	/* We are going to link this sequence to ZoO_WORD_START_OF_LINE */
	sequence[ZoO_MARKOV_ORDER] = ZoO_WORD_START_OF_LINE;

	foreach (i; 1..ZoO_MARKOV_ORDER+1) {
		sequence[ZoO_MARKOV_ORDER - i] = ZoO_WORD_START_OF_LINE;

		if (i <= string.words.length) {
			sequence[ZoO_MARKOV_ORDER + i] = k.learn(string.words[i - 1]);
		} else {
			sequence[ZoO_MARKOV_ORDER + i] = ZoO_WORD_END_OF_LINE;
		}
	}
}

@safe unittest {
	ZoO_knowledge k;
	ZoO_strings str;
	size_t[(ZoO_MARKOV_ORDER * 2) + 1] seq;
	init_sequence(k, str, seq);
	assert(seq[0] == ZoO_WORD_START_OF_LINE);
	assert(seq[$-1] == ZoO_WORD_END_OF_LINE);
}

void ZoO_knowledge_assimilate(ref ZoO_knowledge k, const ZoO_strings string) @safe {
	size_t[(ZoO_MARKOV_ORDER * 2) + 1] sequence;
	size_t next_word, new_word;
	size_t new_word_id;

	debug(learning) trace("Learning phrase ", string);

	if (string.words.length == 0) {
		return;
	}

	init_sequence(k, string, sequence);

	add_word_occurrence(k, sequence);

	next_word = 0;
	new_word = ZoO_MARKOV_ORDER;

	while (next_word <= (string.words.length + ZoO_MARKOV_ORDER)) {
		if (new_word < string.words.length) {
			new_word_id = k.learn(string.words[new_word]);
		} else {
			new_word_id = ZoO_WORD_END_OF_LINE;
		}

		sequence = sequence[1..$]~0;

		sequence[ZoO_MARKOV_ORDER * 2] = new_word_id;

		add_word_occurrence(k, sequence);

		next_word += 1;
		new_word += 1;
	}
}

@safe unittest {
	ZoO_knowledge k;
	ZoO_knowledge_assimilate(k, ZoO_strings());
}
