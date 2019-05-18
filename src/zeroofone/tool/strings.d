module zeroofone.tool.strings;

struct Strings {
	string[] words;

	this(string str) @safe pure {
		parse(str, knowledgePunctuationChars);
	}

	void parse(string input, const string punctuations) @safe pure {
		import std.algorithm.iteration : filter, splitter;
		import std.algorithm.searching : canFind;
		import std.range : empty;
		import std.string : toLower;
		import std.uni : isWhite;

		foreach (split; input.splitter!(x => (x.isWhite || punctuations.canFind(x))).filter!(x => !x.empty)) {
			words ~= split.toLower();
		}
	}
}

immutable string knowledgePunctuationChars = [
	'!',
	',',
	'.',
	':',
	';',
	'?',
	'~'
];

@safe pure unittest {
	import std.algorithm.searching : canFind;
	Strings str;
	str.parse("", "");
	str.parse("test 1 2 3", "");
	assert(str.words.canFind("test", "1", "2", "3"));
	str.parse("7, 8, 9", ",");
	assert(str.words.canFind("7", "8", "9"));
	str.parse("HELLO WORLD", ",");
	assert(str.words.canFind("hello", "world"));
	str.parse("                   yeah                        ", ",");
	assert(str.words.canFind("yeah"));
	assert(!str.words.canFind(""));
	str.words = [];
	str.parse("a", "a");
	assert(!str.words.canFind("a"));
	str.parse("a", "");
	assert(str.words.canFind("a"));
	str.parse("def", "e");
	assert(str.words.canFind("d", "f"));
	assert(!str.words.canFind("e"));
}
