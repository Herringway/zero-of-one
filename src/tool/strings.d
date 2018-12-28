module tool.strings;

import pervasive;
import io.error;

import std.experimental.logger;
import std.string;

struct ZoO_strings {
	string[] words;

	void parse_word(string line) @safe {
		if (line.length == 0) {
			return;
		}

		words ~= line.toLower();
	}

	void parse(string input, const string punctuations) @safe {
		import std.algorithm.iteration : filter, splitter;
		import std.algorithm.searching : canFind;
		import std.range : empty;
		import std.uni : isWhite;

		if (input == null) {
			return;
		}

		while (input[0] == ' ') {
			input = input[1..$];
		}

		if (input[0] == '\001') {
			/* This is an CTCP command. */
			/* We'll remove the trailing '\001' so that only the first word */
			/* indicates the need for CTCP (uppercase) syntax. */

			if ((input.length >= 1) && (input[$ - 1] == '\001')) {
				input = input[0..$ - 1];
			} else {
				warningf("CTCP sequence '%s' did not end with a \\001 character.", input);
			}
		}

		foreach (split; input.splitter!(x => (x.isWhite || punctuations.canFind(x))).filter!(x => !x.empty)) {
			parse_word(split);
		}
	}
}

@safe unittest {
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
}
