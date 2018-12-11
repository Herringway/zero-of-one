module io.data_output;

import core.stdc.errno;
import core.stdc.stdio;
import core.stdc.string;
import std.string;
import std.stdio;
import std.experimental.logger;

import io.error;

int ZoO_data_output_write_line(const string filename, string line) {
	try {
		auto file = File(filename, "a");
		file.writeln(line);
	} catch (StdioException e) {
		error("Error writing to memory file '%s': %s", filename, e.msg);

		return -1;
	}

	return 0;
}
