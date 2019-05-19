module zeroofone.tool.strings;

struct Strings {
	string[] words;

	this(string[] strings) @safe pure {
		words = strings;
	}
	this(string str) @safe pure {
		parse(str);
	}

	void parse(string input) @safe pure {
		words ~= withPunctuationSplit(input);
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
	str.parse("");
	str.parse("test 1 2 3");
	assert(str.words.canFind("test", "1", "2", "3"));
	str.parse("7, 8, 9");
	assert(str.words.canFind("7", "8", "9"));
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

auto withPunctuationSplit(string str) {
	import std.algorithm : canFind;
	import std.array : front;
	import std.uni : isWhite, toLower;
	import std.utf : codeLength;
	string[] result;
	size_t last;
	for (int i; i < str.length; i++) {
		const chr = str[i..$].front;
		const size = chr.codeLength!char;
		const isWhitespace = chr.isWhite;
		if (isWhitespace || knowledgePunctuationChars.canFind(chr)) {
			if (i > last) {
				result ~= str[last..i].toLower();
			}
			if (!isWhitespace) {
				result ~= str[i..i+size];
			}
			last = i+size;
		}
		i += size-1;
	}
	if (last < str.length && !str[last..$].front.isWhite) {
		result ~= str[last..$].toLower();
	}
	return result;
}

@safe unittest {
	assert("yep".withPunctuationSplit == ["yep"]);
}
