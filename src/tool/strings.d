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


	int parse_word(const string punctuations, char[] line) @safe {
		if (line.length == 0) {
			return 0;
		}

		line = line.toLower();

		foreach (punctuation; punctuations) {
			/* overflow-safe: line_size > 1 */
			if (line[$ - 1] == punctuation) {
				if (line.length > 1) {
					if ((add_word(line.idup) < 0) || (add_word(line[$ - 1..$].idup) < 0)) {
						return -1;
					}

					return 0;
				}
			}
		}

		return add_word(line.idup);
	}

	int parse(char[] input, const string punctuations) @safe {
		size_t i, w_start;

		if (input == null) {
			return 0;
		}

		i = 0;

		while (input[i] == ' ') {
			++i;
		}

		w_start = i;

		if (input[i] == '\001') {
			/* This is an CTCP command. */
			/* We'll remove the trailing '\001' so that only the first word */
			/* indicates the need for CTCP (uppercase) syntax. */

			if ((input.length >= 1) && (input[$ - 1] == '\001')) {
				input = input[0..$ - 1];
			} else {
				warningf("CTCP sequence '%s' did not end with a \\001 character.", input);
			}
		}

		for (; i < input.length; ++i) {
			if (input[i] == ' ') {
				if (parse_word(punctuations, input[w_start..i]) < 0) {
					return -1;
				}

				++i;

				while ((i < input.length-1) && (input[i] == ' ')) {
					++i;
				}

				w_start = i;
			}
		}

		if (parse_word(punctuations, input[w_start..i]) < 0) {
			return -1;
		}

		return 0;
	}
}

@safe unittest {
	import std.algorithm.searching : canFind;
	ZoO_strings str;
	assert(str.parse("".dup, "") == 0);
	assert(str.parse("test 1 2 3".dup, "") == 0);
	assert(str.words.canFind("test", "1", "2", "3"));
	assert(str.parse("\001ACTION 4 5 6\001".dup, "") == 0);
	assert(str.words.canFind("\001ACTION", "4", "5", "6"));
	assert(str.parse("7, 8, 9".dup, ",") == 0);
	assert(str.words.canFind("7", "8", "9"));
	assert(str.parse("HELLO WORLD".dup, ",") == 0);
	assert(str.words.canFind("hello", "world"));
	assert(str.parse("                   yeah                        ".dup, ",") == 0);
	assert(str.words.canFind("yeah"));
}
