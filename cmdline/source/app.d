module app;

import std.datetime.stopwatch;
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
	if (help.helpWanted) {
		defaultGetoptPrinter("Zero-of-One markov chain bot, Herringway edition.", help.options);
		return;
	}
	sharedLog = new FileLogger("log.txt");
	infof("Memory file: %s (read-only: %s)", memoryFile, readonly);
	Knowledge knowledge;

	auto stopWatch = StopWatch(AutoStart.yes);
	foreach (file; args[1..$].chain(only(memoryFile))) {
		write("Learning ", file, ", ");
		learnFile(knowledge, file);
	}
	stopWatch.stop();
	writeln("Learning completed in ", stopWatch.peek, ".");
	writeln("Optimizing knowledge...");

	knowledge.optimize();

	while(true) {
		write("> ");
		auto input = readln().strip();
		auto str = parse(input.dup);

		if (str.length == 0) {
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
	write("line 0");
	ulong digits = 1;
	ulong tens = 1;
	foreach (i, str; File(file, "r").byLineCopy().enumerate) {
		if (tens*10 < i) {
			digits++;
			tens *= 10;
		}
		knowledge.learnString(str);
		if (i%2 == 0) {
			writef!"%-(%s%)%s"("\b".repeat(digits), i);
		}
	}
	writeln();
}
