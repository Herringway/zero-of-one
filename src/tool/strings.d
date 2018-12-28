module tool.strings;

struct ZoO_strings {
	string[] words;

	void parse(string input, const string punctuations) @safe pure {
		import std.algorithm.iteration : filter, splitter;
		import std.algorithm.searching : canFind, endsWith, startsWith;
		import std.range : empty;
		import std.string : toLower;
		import std.uni : isWhite;

		/* This is a CTCP command. */
		/* We'll remove the trailing '\001' so that only the first word */
		/* indicates the need for CTCP (uppercase) syntax. */
		if ((input.length > 1) && input.startsWith('\001') && input.endsWith('\001')) {
			input = input[0..$ - 1];
		}

		foreach (split; input.splitter!(x => (x.isWhite || punctuations.canFind(x))).filter!(x => !x.empty)) {
			words ~= split.toLower();
		}
	}
}

@safe pure unittest {
	import std.algorithm.searching : canFind;
	ZoO_strings str;
	str.parse("", "");
	str.parse("test 1 2 3", "");
	assert(str.words.canFind("test", "1", "2", "3"));
	str.parse("\001ACTION 4 5 6\001", "");
	assert(str.words.canFind("\001ACTION", "4", "5", "6"));
	str.parse("7, 8, 9", ",");
	assert(str.words.canFind("7", "8", "9"));
	str.parse("HELLO WORLD", ",");
	assert(str.words.canFind("hello", "world"));
	str.parse("                   yeah                        ", ",");
	assert(str.words.canFind("yeah"));
	assert(!str.words.canFind(""));
	str.parse("\001\001", "");
	assert(str.words.canFind("\001"));
	str.words = [];
	str.parse("\001", "");
	assert(str.words.canFind("\001"));
}
