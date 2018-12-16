module tool.strings;

import pervasive;
import io.error;

import std.experimental.logger;
import std.string;

struct ZoO_strings {
	string[] words;

	int add_word(string line) @safe {
		if (words.length == ZoO_INDEX_MAX) {
			warning("Data input sentence has too many words.");

			return -1;
		}

		words.length++;

		words[$-1] = line.idup;

		return 0;
	}


	int parse_word(const string punctuations, char[] line) @safe {
		ZoO_index j;

		if (line.length == 0) {
			return 0;
		}

		for (j = 0; j < line.length; ++j) {
			switch (line[j]) {
				case 'A':
				case 'B':
				case 'C':
				case 'D':
				case 'E':
				case 'F':
				case 'G':
				case 'H':
				case 'I':
				case 'J':
				case 'K':
				case 'L':
				case 'M':
				case 'N':
				case 'O':
				case 'P':
				case 'Q':
				case 'R':
				case 'S':
				case 'T':
				case 'U':
				case 'V':
				case 'W':
				case 'X':
				case 'Y':
				case 'Z':
					line[j] = cast(char)('z' - ('Z' - line[j]));
					break;

				default:
					break;
			}
		}

		for (j = 0; j < punctuations.length; ++j) {
			/* overflow-safe: line_size > 1 */
			if (line[$ - 1] == punctuations[j]) {
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

		/* overflow-safe: input is '\0' terminated. */
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

				/* safe, as input is terminated by '\0' */
				while (input[i] == ' ') {
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
