module tool.strings;

import pervasive;
import io.error;

import core.stdc.stdlib;
import core.stdc.string;
import std.experimental.logger;
import std.string;

struct ZoO_strings {
	ZoO_index words_count;
	ZoO_char ** words;
	size_t * word_sizes;

	void initialize() {
		words_count = 0;
		words = null;
		word_sizes = null;
	}

	void finalize() {
		if (words_count != 0) {
			ZoO_index i;

			words_count = 0;

			words = null;
			word_sizes = null;
		}
	}

	int add_word(char[] line) {
		size_t * new_s_word_sizes;
		ZoO_char* new_word;
		ZoO_char** new_s_words;

		if (words_count == ZoO_INDEX_MAX) {
			warning("Data input sentence has too many words.");

			return -1;
		}

		/* overflow-safe, as line_size < SIZE_MAX */
		new_word = cast(ZoO_char *) calloc((line.length + 1), ZoO_char.sizeof);

		if (new_word == null) {
			warning("Unable to allocate memory to extract new word.");

			return -1;
		}

		memcpy(new_word, line.ptr, line.length);

		new_word[line.length] = '\0';

		new_s_words = cast(ZoO_char **) realloc(words, ((ZoO_char *).sizeof * (words_count + 1)));

		if (new_s_words == null) {
			warning("Unable to reallocate memory to extract new word.");

			return -1;
		}

		words = new_s_words;

		new_s_word_sizes = cast(size_t *) realloc(word_sizes, (size_t.sizeof * (words_count + 1))	);

		if (new_s_word_sizes == null) {
			warning("Unable to reallocate memory to extract new word.");

			return -1;
		}

		word_sizes = new_s_word_sizes;

		words[words_count] = new_word;
		word_sizes[words_count] = (line.length + 1);

		words_count += 1;

		return 0;
	}


	int parse_word(const ZoO_index punctuations_count, const ZoO_char* punctuations, char[] line) {
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

		for (j = 0; j < punctuations_count; ++j) {
			/* overflow-safe: line_size > 1 */
			if (line[$ - 1] == punctuations[j]) {
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

	int parse(char[] input, const ZoO_index* punctuations_count, const ZoO_char* punctuations)
	{
		size_t i, w_start;

		finalize();

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
				if (parse_word(*punctuations_count, punctuations, input[w_start..i]) < 0) {
					finalize();

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

		if (parse_word(*punctuations_count, punctuations, input[w_start..i]) < 0) {
			finalize();

			return -1;
		}

		return 0;
	}
}
