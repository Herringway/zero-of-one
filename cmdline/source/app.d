module app;

import std.experimental.logger;
import std.stdio;
import std.string;

import zeroofone;

enum memoryFile = "memory.txt";

void main() {
	ZoO_knowledge knowledge;

	foreach (str; File(memoryFile, "r").byLineCopy()) {
		knowledge.learnString(str);
	}

	while(true) {
		auto input = readln().strip();
		ZoO_strings str;
		str.parse(input.dup, ZoO_knowledge_punctuation_chars);

		if (str.words.length == 0) {
			//break;
		}
		File(memoryFile, "a").writeln(input);
		auto line = ZoO_knowledge_extend(knowledge, str, [], false);
		writeln(line);
		knowledge.learnString(input);
	}
}
