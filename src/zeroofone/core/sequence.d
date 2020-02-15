module zeroofone.core.sequence;

import zeroofone.core.knowledge;

struct KnowledgeLinkSequence {
	import std.algorithm.comparison : max;
	enum Size = max(SentenceSequence.MarkovOrder - 1, 1);
	size_t[Size] sequence;
	alias sequence this;
}

struct SentenceSequence {
	enum MarkovOrder = 3;
	enum Size = (MarkovOrder * 2) + 1;
	size_t[Size] sequence = Knowledge.terminator;
	alias sequence this;

	const startPoint() @safe pure {
		return sequence[MarkovOrder];
	}
	auto firstHalf() inout @safe pure {
		return HalfSentenceSequence(sequence[0..MarkovOrder]);
	}
	auto secondHalf() inout @safe pure {
		return HalfSentenceSequence(sequence[MarkovOrder + 1..$]);
	}
	auto getKnowledgeLink(ptrdiff_t relative) const @safe pure {
		ulong[KnowledgeLinkSequence.Size] tmp = sequence[MarkovOrder + relative .. MarkovOrder + relative + KnowledgeLinkSequence.Size];
		return KnowledgeLinkSequence(tmp);
	}
	void pushLeft(size_t id) @safe pure @nogc nothrow {
		foreach (i; 0 .. Size - 1) {
			sequence[i] = sequence[i + 1];
		}
		sequence[$ - 1] = id;
	}
}

@safe pure unittest {
	with(SentenceSequence([1, 2, 3, 4, 5, 6, 7])) {
		pushLeft(0);
		assert(sequence == [2, 3, 4, 5, 6, 7, 0]);
	}
}

struct HalfSentenceSequence {
	size_t[SentenceSequence.MarkovOrder] sequence;
	alias sequence this;
	void pushLeft(size_t id) @safe pure @nogc nothrow {
		foreach (i; 0 .. SentenceSequence.MarkovOrder - 1) {
			sequence[i] = sequence[i + 1];
		}
		sequence[$ - 1] = id;
	}
	void pushRight(size_t id) @safe pure @nogc nothrow {
		foreach_reverse (i; 1 .. SentenceSequence.MarkovOrder) {
			sequence[i] = sequence[i - 1];
		}
		sequence[0] = id;
	}
	auto asKnowledgeLinkSequenceLeft() const @safe pure {
		return KnowledgeLinkSequence(sequence[1 .. $]);
	}
	auto asKnowledgeLinkSequenceRight() const @safe pure {
		return KnowledgeLinkSequence(sequence[0 .. $ - 1]);
	}
}

@safe pure unittest {
	with(HalfSentenceSequence([1, 2, 3])) {
		pushLeft(0);
		assert(sequence == [2, 3, 0]);
	}
	with(HalfSentenceSequence([1, 2, 3])) {
		pushRight(0);
		assert(sequence == [0, 1, 2]);
	}
}
