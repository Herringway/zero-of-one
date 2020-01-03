module zeroofone.tool.strings;

import zeroofone.core.knowledge;

struct Strings {
	string[] words;

	this(string[] strings) @safe pure {
		words = strings;
	}
	this(string str) @safe pure {
		parse(str);
	}

	void parse(string input) @safe pure {
		import std.algorithm : canFind;
		import std.array : front;
		import std.uni : isPunctuation, isWhite, toLower;
		import std.utf : codeLength;
		size_t last;
		for (int i; i < input.length; i++) {
			const chr = input[i..$].front;
			const size = chr.codeLength!char;
			const isWhitespace = chr.isWhite;
			if (isWhitespace || chr.isPunctuation) {
				if (i > last) {
					words ~= input[last..i].toLower();
				}
				if (!isWhitespace) {
					words ~= input[i..i+size];
				}
				last = i+size;
			}
			i += size-1;
		}
		if (last < input.length && !input[last..$].front.isWhite) {
			words ~= input[last..$].toLower();
		}
	}
}

immutable string knowledgePunctuationCharsRemovesRightSpace = [
	',',
	':',
	';',
	'~'
];

immutable string knowledgePunctuationCharsNextCapitalized = [
	'?',
	'!',
	'.'
];

SpecialEffect specialEffect(dchar c) @safe pure {
	import std.algorithm.searching : canFind;
	import std.uni : isPunctuation;
	if (c.isPunctuation) {
		if (knowledgePunctuationCharsNextCapitalized.canFind(c)) {
			return SpecialEffect.REMOVES_LEFT_SPACE_CAPITALIZES_NEXT_WORD;
		}
		return SpecialEffect.REMOVES_LEFT_SPACE;
	}
	return SpecialEffect.HAS_NO_EFFECT;
}

immutable string knowledgePunctuationChars = knowledgePunctuationCharsRemovesRightSpace~knowledgePunctuationCharsNextCapitalized;

@safe pure unittest {
	import std.algorithm.searching : canFind;
	Strings str;
	str.parse("");
	str.parse("test 1 2 3");
	assert(str.words.canFind("test", "1", "2", "3"));
	str.parse("7, 8, 9");
	assert(str.words.canFind("7", "8", "9", ","));
	str.parse("HELLO WORLD");
	assert(str.words.canFind("hello", "world"));
	str.parse("                   yeah                        ");
	assert(str.words.canFind("yeah"));
	assert(!str.words.canFind(""));
	str.words = [];
	str.parse("a");
	assert(str.words.canFind("a"));
	str.parse("def");
	assert(str.words.canFind("def"));
}
