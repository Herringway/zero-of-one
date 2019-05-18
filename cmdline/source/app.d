module app;

import std.experimental.logger;
import std.getopt;
import std.range;
import std.stdio;
import std.string;

import zeroofone;

enum memoryFile = "memory.txt";

void main(string[] args) {
	bool readonly;
	auto help = getopt(args,
		"readonly|r", "Don't write to memory file", &readonly
	);
	sharedLog = new FileLogger("log.txt");
	infof("Memory file: %s (read-only: %s)", memoryFile, readonly);
	Knowledge knowledge;

	foreach (file; args[1..$].chain(only(memoryFile))) {
		writeln("Learning ", file);
		learnFile(knowledge, file);
	}
	writeln("Learning complete.");

	while(true) {
		write("> ");
		auto input = readln().strip();
		auto str = Strings(input.dup);

		if (str.words.length == 0) {
			continue;
		}
		if (!readonly) {
			File(memoryFile, "a").writeln(input);
		}
		auto line = knowledgeExtend(knowledge, str, false);
		writeln(line);
		if (!readonly) {
			knowledge.learnString(input);
		}
	}
}

void learnFile(ref Knowledge knowledge, string file) {
	write("Learning line #");
	ulong digits = 1;
	ulong tens = 1;
	foreach (i, str; File(file, "r").byLineCopy().enumerate) {
		if (tens*10 < i) {
			digits++;
			tens *= 10;
		}
		knowledge.learnString(str);
		writef!"%-(%s%)%s"("\b".repeat(digits), i);
	}
	writeln();
}
