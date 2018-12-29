module io.data_input;

import std.experimental.logger;
import std.stdio;
import std.string;

import tool.strings;
import io.error;

import pervasive;

struct ZoO_data_input {
	File file;
	ZoO_strings str;

	int open(const string filename) @safe {
		try {
			file = File(filename, "r");
		} catch (Exception) {
			errorf("Could not open file '%s' in readonly mode.", filename);

			return -1;
		}

		return 0;
	}

	int read_line(const string punctuations) @system {
		size_t i, w_start;
		char[] line;

		line = null;

		if (file.readln(line) < 1) {
			return -1;
		}

		str = ZoO_strings.init;
		str.parse(line[0..$-1].idup, punctuations);

		return 0;
	}


	void close() @safe {
		file.close();
	}
}