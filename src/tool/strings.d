module tool.strings;

import pervasive;
import io.error;
import tool.strings_types;

import core.stdc.stdlib;
import core.stdc.string;

void ZoO_strings_initialize(ZoO_strings* s) {
	s.words_count = 0;
	s.words = null;
	s.word_sizes = null;
}

void ZoO_strings_finalize(ZoO_strings* s) {
	if (s.words_count != 0) {
		ZoO_index i;

		for (i = 0; i < s.words_count; ++i) {
			free(s.words[i]);
		}

		s.words_count = 0;

		free(s.words);
		free(s.word_sizes);

		s.words = null;
		s.word_sizes = null;
	}
}

int add_word(ZoO_strings* s, const size_t line_size, const ZoO_char* line) {
	size_t * new_s_word_sizes;
	ZoO_char* new_word;
	ZoO_char** new_s_words;

	if (s.words_count == ZoO_INDEX_MAX) {
		ZoO_S_WARNING("Data input sentence has too many words.");

		return -1;
	}

	/* overflow-safe, as line_size < SIZE_MAX */
	new_word = cast(ZoO_char *) calloc((line_size + 1), ZoO_char.sizeof);

	if (new_word == null) {
		ZoO_S_WARNING("Unable to allocate memory to extract new word.");

		return -1;
	}

	memcpy(new_word, line, line_size);

	new_word[line_size] = '\0';

	new_s_words = cast(ZoO_char **) realloc(s.words, ((ZoO_char *).sizeof * (s.words_count + 1)));

	if (new_s_words == null) {
		ZoO_S_WARNING("Unable to reallocate memory to extract new word.");

		free(new_word);

		return -1;
	}

	s.words = new_s_words;

	new_s_word_sizes = cast(size_t *) realloc(s.word_sizes, (size_t.sizeof * (s.words_count + 1))	);

	if (new_s_word_sizes == null) {
		ZoO_S_WARNING("Unable to reallocate memory to extract new word.");

		free(new_word);

		return -1;
	}

	s.word_sizes = new_s_word_sizes;

	s.words[s.words_count] = new_word;
	s.word_sizes[s.words_count] = (line_size + 1);

	s.words_count += 1;

	return 0;
}


int parse_word(ZoO_strings* s, const ZoO_index punctuations_count, const ZoO_char* punctuations, const size_t line_size, ZoO_char* line) {
	ZoO_index j;

	if (line_size == 0) {
		return 0;
	}

	for (j = 0; j < line_size; ++j) {
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
		if (line[line_size - 1] == punctuations[j]) {
			if (line_size > 1) {
				if ((add_word(s, (line_size - 1), line) < 0) || (add_word(s, 1, (line + (line_size - 1))) < 0)) {
					return -1;
				}

				return 0;
			}
		}
	}

	return add_word(s, line_size, line);
}

int ZoO_strings_parse(ZoO_strings* s, size_t input_size, ZoO_char* input, const ZoO_index* punctuations_count, const ZoO_char* punctuations)
{
	size_t i, w_start;

	ZoO_strings_finalize(s);

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

		if ((input_size >= 1) && (input[input_size - 1] == '\001')) {
			input[input_size - 1] = ' ';
		} else {
			ZoO_WARNING("CTCP sequence '%s' did not end with a \\001 character.", input);
		}
	}

	for (; i < input_size; ++i) {
		if (input[i] == ' ') {
			if (parse_word(s, *punctuations_count, punctuations, (i - w_start),(input + w_start)) < 0) {
				ZoO_strings_finalize(s);

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

	if (parse_word(s, *punctuations_count, punctuations, (i - w_start), (input + w_start)) < 0) {
		ZoO_strings_finalize(s);

		return -1;
	}

	return 0;
}

