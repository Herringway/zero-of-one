module app;

import std.experimental.logger;
import std.stdio;
import std.string;

import pervasive;
import io.parameters;
import io.data_input;
import io.data_output;
import io.error;
import tool.strings;
import core.assimilate;
import core.create_sentences;
import core.knowledge;

struct ZoO_state {
	ZoO_parameters param;
	ZoO_knowledge knowledge;


	int load_data_file() {
		ZoO_data_input input;
		char* result;

		if (input.open(param.data_filename) < 0) {
			return -1;
		}

		while (input.read_line(ZoO_knowledge_punctuation_chars) == 0) {
			ZoO_knowledge_assimilate(knowledge, input.str, param.aliases);
		}

		input.close();

		return 0;
	}
}

void main() {
	ZoO_state state;
	ZoO_strings str;

	state.load_data_file();

	while(true) {
		auto input = readln().strip();
		str.parse(input.dup, ZoO_knowledge_punctuation_chars);

		if (str.words.length == 0) {
			//break;
		}
		if (ZoO_data_output_write_line(state.param.new_data_filename, input) != 0) {
			break;
		}
		string line;
		ZoO_knowledge_extend(state.knowledge, &str, state.param.aliases, line);
		writeln(line.strip);
		ZoO_knowledge_assimilate(state.knowledge, str, state.param.aliases);
	}
}