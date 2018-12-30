module core.sequence;

import core.stdc.string;

import core.knowledge;

import tool.sorted_list;

import pervasive;

int cmp_seq_link(const size_t[] sequence, const ZoO_knowledge_link link, const typeof(null)) @safe {
	size_t j;
	for (j = 0; j < ZoO_SEQUENCE_SIZE; ++j) {
		if (sequence[j] < link.sequence[j]) {
			return -1;
		} else if (sequence[j] > link.sequence[j]) {
			return 1;
		}
	}

	return 0;
}

int ZoO_knowledge_find_link(const ZoO_knowledge_link[] links, const size_t[] sequence, out size_t result) @safe {
	return ZoO_sorted_list_index_of!cmp_seq_link(links, sequence, null, result);
}

int ZoO_knowledge_get_link(ref ZoO_knowledge_link[] links, const size_t[] sequence, out size_t result) @safe {
	if (ZoO_sorted_list_index_of!cmp_seq_link(links, sequence, null, result) == 0) {
		return 0;
	}
	links.length += 1;

	if (result < (links.length - 1)) {
		links = links[0..result+1]~links[result..$-1];
	}

	links[result].sequence = sequence[0..2];
	links[result].targets_occurrences = null;
	links[result].targets = null;

	return 0;
}

@system unittest {
	import std.stdio;
	ZoO_knowledge_link[] links =[ZoO_knowledge_link([10, 11], [1], [0]), ZoO_knowledge_link([10, 11], [1], [0])];
	size_t[] sequence;
	size_t result;

	assert(ZoO_knowledge_get_link(links, [1,1,1,1,1,1], result) == 0);
	assert(result == 0);
	assert(links == [ZoO_knowledge_link([1, 1], [], []), ZoO_knowledge_link([10, 11], [1], [0]), ZoO_knowledge_link([10, 11], [1], [0])]);
}
