module io.error;

import pervasive;
import std.stdio;

enum ZoO_DEBUG_ALL = 1;

enum ZoO_DEBUG_PROGRAM_FLOW = (0 || ZoO_DEBUG_ALL);

enum ZoO_DEBUG_CONFIG = (0 || ZoO_DEBUG_ALL);

enum ZoO_DEBUG_LEARNING = (0 || ZoO_DEBUG_ALL);

enum ZoO_DEBUG_NETWORK = 1;
enum ZoO_DEBUG_NETWORK_PING = 0;
enum ZoO_RANDOMLY_IGNORE_PING = 0;

enum ZoO_ENABLE_WARNINGS_OUTPUT = 1;
enum ZoO_ENABLE_RUNTIME_ERRORS_OUTPUT = 1;
enum ZoO_ENABLE_PROGRAMMING_ERRORS_OUTPUT = 1;
enum ZoO_ENABLE_FATAL_ERROR_OUTPUT = 1;

/*
 * Given that we use preprocessor contants as flags, we can expect the compilers
 * to remove the test condition for disabled flags. No need to be shy about
 * allowing many debug options.
 */

void ZoO_DEBUG(T...)(bool flag, string fmt, T args) {
	if (flag) {
		stderr.writefln("[D] "~fmt, args);
	}
}

void ZoO_WARNING(T...)(string fmt, T args) {
	stderr.writefln("[W] "~fmt, args);
}

void ZoO_ERROR(T...)(string fmt, T args) {
	stderr.writefln("[E] "~fmt, args);
}

void ZoO_PROG_ERROR(T...)(string fmt, T args) {
	stderr.writefln("[P] "~fmt, args);
}

void ZoO_FATAL(T...)(string fmt, T args) {
	stderr.writefln("[F] "~fmt, args);
}

/* For outputs without dynamic content (static). ******************************/

// #define ZoO_PRINT_S_STDERR(symbol, str)\
//    fprintf(stderr, "[" symbol "]" ZoO_LOCATION " " str "\n");

void ZoO_S_DEBUG(bool flag, string str) {
	if (flag) {
		stderr.writeln("[D] ", str);
	}
}

void ZoO_S_WARNING(string str) {
	stderr.writeln("[W] ", str);
}

void ZoO_S_ERROR(string str) {
	stderr.writeln("[E] ", str);
}

void ZoO_S_PROG_ERROR(string str) {
	stderr.writeln("[P] ", str);
}

void ZoO_S_FATAL(string str) {
	stderr.writeln("[F] ", str);
}
