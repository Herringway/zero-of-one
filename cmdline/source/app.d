module app;

import std.experimental.logger;
import std.range;
import std.stdio;
import std.string;

import zeroofone;

enum memoryFile = "memory.txt";

void main() {
	sharedLog = new FileLogger("log.txt");
	ZoO_knowledge knowledge;

	write("Learning line #");
	ulong digits = 1;
	ulong tens = 1;
	foreach (i, str; File(memoryFile, "r").byLineCopy().enumerate) {
		if (tens*10 < i) {
			digits++;
			tens *= 10;
		}
		knowledge.learnString(str);
		writef!"%-(%s%)%s"("\b".repeat(digits), i);
	}
	writeln();
	writeln("Learning complete.");

	while(true) {
		write("> ");
		auto input = readln().strip();
		ZoO_strings str;
		str.parse(input.dup, ZoO_knowledge_punctuation_chars);

		if (str.words.length == 0) {
			continue;
		}
		File(memoryFile, "a").writeln(input);
		auto line = ZoO_knowledge_extend(knowledge, str, false);
		writeln(line);
		knowledge.learnString(input);
	}
}
