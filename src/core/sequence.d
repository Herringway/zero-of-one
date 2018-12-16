module core.sequence;

import core.stdc.stdlib;
import core.stdc.string;

import core.knowledge;

import tool.sorted_list;

import pervasive;

int cmp_seq_link(const ZoO_index[] sequence, const ZoO_knowledge_link link, const typeof(null)) @safe {
	ZoO_index j;
	for (j = 0; j < ZoO_SEQUENCE_SIZE; ++j) {
		if (sequence[j] < link.sequence[j]) {
			return -1;
		} else if (sequence[j] > link.sequence[j]) {
			return 1;
		}
	}

	return 0;
}

int ZoO_knowledge_find_link(ref ZoO_knowledge_link[] links, const ZoO_index[] sequence, out ZoO_index result) @safe {
	return ZoO_sorted_list_index_of(links, sequence, &cmp_seq_link, null, result);
}

int ZoO_knowledge_get_link(ref ZoO_knowledge_link[] links, const ZoO_index[] sequence, out ZoO_index result) {
	if (ZoO_sorted_list_index_of(links, sequence, &cmp_seq_link, null, result) == 0) {
		return 0;
	}
	links.length += 1;

	if (result < (links.length - 1)) {
		memmove(&links[result + 1], &links[result], (ZoO_knowledge_link.sizeof * (links.length - 1 - result)));
	}

	links[result].sequence = sequence;
	links[result].targets_occurrences = null;
	links[result].targets = null;

	return 0;
}