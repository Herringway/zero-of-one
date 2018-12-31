module io.data_output;

import std.string;
import std.stdio;
import std.experimental.logger;

int ZoO_data_output_write_line(const string filename, string line) @safe {
	try {
		auto file = File(filename, "a");
		file.writeln(line);
	} catch (StdioException e) {
		error("Error writing to memory file '%s': %s", filename, e.msg);

		return -1;
	}

	return 0;
}
