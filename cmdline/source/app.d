module app;

import std.experimental.logger;
import std.stdio;
import std.string;

import pervasive;
import io.data_input;
import io.data_output;
import tool.strings;
import core.assimilate;
import core.create_sentences;
import core.knowledge;

enum memoryFile = "memory.txt";

struct ZoO_state {
	ZoO_knowledge knowledge;


	int load_data_file() {
		ZoO_data_input input;
		char* result;

		if (input.open(memoryFile) < 0) {
			return -1;
		}

		while (input.read_line(ZoO_knowledge_punctuation_chars) == 0) {
			ZoO_knowledge_assimilate(knowledge, input.str);
		}

		input.close();

		return 0;
	}
}

void main() {
	ZoO_state state;

	state.load_data_file();

	while(true) {
		auto input = readln().strip();
		ZoO_strings str;
		str.parse(input.dup, ZoO_knowledge_punctuation_chars);

		if (str.words.length == 0) {
			//break;
		}
		if (ZoO_data_output_write_line(memoryFile, input) != 0) {
			break;
		}
		auto line = ZoO_knowledge_extend(state.knowledge, str, [], false);
		writeln(line);
		state.knowledge.learnString(input);
	}
}