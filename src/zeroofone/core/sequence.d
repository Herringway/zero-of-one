module zeroofone.core.sequence;

import zeroofone.core.knowledge;

import zeroofone.tool.sorted_list;

struct KnowledgeLinkSequence {
	import std.algorithm.comparison : max;
	enum Size = max(SentenceSequence.MarkovOrder - 1, 1);
	size_t[Size] sequence;
	alias sequence this;
}

struct SentenceSequence {
	enum MarkovOrder = 3;
	enum Size = (MarkovOrder * 2) + 1;
	size_t[Size] sequence;
	alias sequence this;

	const startPoint() @safe {
		return sequence[MarkovOrder];
	}
	auto firstHalf() inout @safe {
		return HalfSentenceSequence(sequence[0..MarkovOrder]);
	}
	auto secondHalf() inout @safe {
		return HalfSentenceSequence(sequence[MarkovOrder + 1..$]);
	}
	auto getKnowledgeLink(ptrdiff_t relative) inout @safe {
		return sequence[MarkovOrder + relative .. MarkovOrder + relative + KnowledgeLinkSequence.Size];
	}
}

struct HalfSentenceSequence {
	size_t[SentenceSequence.MarkovOrder] sequence;
	alias sequence this;
}


size_t getKnowledgeLinks(ref KnowledgeLink[] links, const KnowledgeLinkSequence sequence) @safe {
	static int cmpSeqLink(const size_t[] sequence, const KnowledgeLink link, const typeof(null)) @safe {
		size_t j;
		for (j = 0; j < KnowledgeLinkSequence.Size; ++j) {
			if (sequence[j] < link.sequence[j]) {
				return -1;
			} else if (sequence[j] > link.sequence[j]) {
				return 1;
			}
		}

		return 0;
	}
	size_t result;
	if (binarySearch!cmpSeqLink(links, sequence, null, result) == 0) {
		return result;
	}
	links.length += 1;

	if (result < (links.length - 1)) {
		links = links[0..result+1]~links[result..$-1];
	}

	links[result].sequence = sequence;
	links[result].targetsOccurrences = null;
	links[result].targets = null;
	return result;
}

@safe unittest {
	KnowledgeLink[] links =[KnowledgeLink(KnowledgeLinkSequence([10, 11]), [1], [0]), KnowledgeLink(KnowledgeLinkSequence([10, 11]), [1], [0])];

	assert(getKnowledgeLinks(links, KnowledgeLinkSequence([1,1])) == 0);
	assert(links == [KnowledgeLink(KnowledgeLinkSequence([1, 1]), [], []), KnowledgeLink(KnowledgeLinkSequence([10, 11]), [1], [0]), KnowledgeLink(KnowledgeLinkSequence([10, 11]), [1], [0])]);
}
