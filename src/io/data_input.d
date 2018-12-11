module io.data_input;

import core.stdc.stdio;
import core.stdc.stdlib;
import core.stdc.string;
import core.sys.posix.stdio: getline;
import std.string;

import tool.strings;
import io.data_input_types;
import io.error;

import pervasive;

int ZoO_data_input_open (ZoO_data_input* di, const string filename) {
	ZoO_strings_initialize(&(di.string));

	di.file = fopen(filename.toStringz, "r");

	if (di.file == null) {
		ZoO_ERROR("Could not open file '%s' in readonly mode.", filename);

		return -1;
	}

	return 0;
}

int ZoO_data_input_read_line(ZoO_data_input* di, const ZoO_index punctuations_count, const ZoO_char* punctuations) {
	size_t line_size, i, w_start;
	ZoO_char * line;

	ZoO_strings_finalize(&(di.string));

	line = null;
	line_size = 0;

	/* XXX: assumed compatible with ZoO_char */

	if (getline(&line, &line_size, di.file) < 1) {
		free(line);

		return -1;
	}

	line_size = strlen(line);
	line[line_size - 1] = '\0';

	--line_size; /* removed '\n' */

	if (ZoO_strings_parse (&(di.string), line_size, line, &punctuations_count, punctuations) < 0) {
		free(line);

		return -1;
	}

	free(line);

	return 0;
}


void ZoO_data_input_close (ZoO_data_input* di) {
	if (di.file != null) {
		fclose(di.file);

		di.file = null;
	}

	ZoO_strings_finalize(&(di.string));
}