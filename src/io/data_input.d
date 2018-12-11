module io.data_input;

import std.experimental.logger;
import std.stdio;
import std.string;

import tool.strings;
import io.data_input_types;
import io.error;

import pervasive;

int ZoO_data_input_open (ZoO_data_input* di, const string filename) {
	di.string.initialize();

	try {
		di.file = File(filename, "r");
	} catch (Exception) {
		error("Could not open file '%s' in readonly mode.", filename);

		return -1;
	}

	return 0;
}

int ZoO_data_input_read_line(ZoO_data_input* di, const ZoO_index punctuations_count, const ZoO_char* punctuations) {
	size_t i, w_start;
	ZoO_char[] line;

	di.string.finalize();

	line = null;

	if (di.file.readln(line) < 1) {
		return -1;
	}

	if (di.string.parse(line[0..$-1], &punctuations_count, punctuations) < 0) {
		return -1;
	}

	return 0;
}


void ZoO_data_input_close (ZoO_data_input* di) {
	di.file.close();

	di.string.finalize();
}