module tool.strings;

import pervasive;
import io.error;

import std.experimental.logger;
import std.string;

struct ZoO_strings {
	string[] words;

	int add_word(string line) @safe {
		if (words.length == size_t.max) {
			warning("Data input sentence has too many words.");

			return -1;
		}

		words.length++;

		words[$-1] = line;

		return 0;
	}


	int parse_word(const string punctuations, string line) @safe {
		if (line.length == 0) {
			return 0;
		}

		line = line.toLower();

		foreach (punctuation; punctuations) {
			/* overflow-safe: line_size > 1 */
			if (line[$ - 1] == punctuation) {
				if (line.length > 1) {
					if ((add_word(line) < 0) || (add_word(line[$ - 1..$]) < 0)) {
						return -1;
					}

					return 0;
				}
			}
		}

		return add_word(line);
	}

	int parse(string input, const string punctuations) @safe {
		import std.algorithm.iteration : filter, splitter;
		import std.algorithm.searching : canFind;
		import std.range : empty;
		import std.uni : isWhite;
		size_t i, w_start;

		if (input == null) {
			return 0;
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
			if (parse_word(punctuations, split) < 0) {
				return -1;
			}
		}

		return 0;
	}
}

@safe unittest {
	import std.algorithm.searching : canFind;
	ZoO_strings str;
	assert(str.parse("", "") == 0);
	assert(str.parse("test 1 2 3", "") == 0);
	assert(str.words.canFind("test", "1", "2", "3"));
	assert(str.parse("\001ACTION 4 5 6\001", "") == 0);
	assert(str.words.canFind("\001ACTION", "4", "5", "6"));
	assert(str.parse("7, 8, 9", ",") == 0);
	assert(str.words.canFind("7", "8", "9"));
	assert(str.parse("HELLO WORLD", ",") == 0);
	assert(str.words.canFind("hello", "world"));
	assert(str.parse("                   yeah                        ", ",") == 0);
	assert(str.words.canFind("yeah"));
	assert(!str.words.canFind(""));
}
