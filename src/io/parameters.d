module io.parameters;

import core.stdc.string;
import core.stdc.stdio;
import core.stdc.stdlib;
import core.stdc.errno;
import std.stdio;
import std.string;
import std.experimental.logger;

import io.parameters_types;
import io.error;

import pervasive;

void load_default_parameters(ref ZoO_parameters param) {
	param.data_filename        = ZoO_DEFAULT_DATA_FILENAME;
	param.new_data_filename    = null;

	param.irc_server_addr     = ZoO_DEFAULT_IRC_SERVER_ADDR;
	param.irc_server_port     = ZoO_DEFAULT_IRC_SERVER_PORT;
	param.irc_server_channel  = ZoO_DEFAULT_IRC_SERVER_CHANNEL;
	param.irc_username        = ZoO_DEFAULT_IRC_USERNAME;
	param.irc_realname        = ZoO_DEFAULT_IRC_REALNAME;

	param.reply_rate          = ZoO_DEFAULT_REPLY_RATE;

	param.aliases = [];
}

void print_help (const string exec) {
	writefln(
		"Usage: %s [option_1 option_2 ...] NICKNAME [ALIAS_1 ALIAS_2 ...] \n"~
		"NICKNAME is used as the IRC nickname value.\n"~
		"If NICKNAME or any ALIAS is found in an event, the program will reply.\n"~
		"\nAvailable options:\n"~
		"   [--data-filename | -df] FILENAME\n"~
		"      Learn content from FILENAME before connecting.\n"~
		"      Default: %s.\n"~
		"   [--new-data-filename | -ndf] FILENAME\n"~
		"      Store new data learned in FILENAME.\n"~
		"      Default: value of the --data-filename param.\n"~
		"   [--irc-server-addr | -isa] IRC_SERVER_ADDR\n"~
		"      Connect to this server address.\n"~
		"      Default: %s.\n"~
		"   [--irc-server-port | -isp] IRC_SERVER_PORT\n"~
		"      Connect to this server port.\n"~
		"      Default: %s.\n"~
		"   [--irc-server-channel | -isc] IRC_SERVER_CHANNEL\n"~
		"      Connect to this server's channel.\n"~
		"      Default: %s.\n"~
		"   [--irc-username | -iu] USERNAME\n"~
		"      Connect using this as 'username' (shown in WHOIS).\n"~
		"      Default: %s.\n"~
		"   [--irc-realname | -ir] REALNAME\n"~
		"      Connect using this as 'realname' (shown in WHOIS).\n"~
		"      Default: %s.\n"~
		"   [--reply-rate | -rr] REPLY_RATE\n"~
		"      Chance to reply to an event (integer, range [0, 100]).\n"~
		"      Default: %d.\n",
		exec,
		ZoO_DEFAULT_DATA_FILENAME,
		ZoO_DEFAULT_IRC_SERVER_ADDR,
		ZoO_DEFAULT_IRC_SERVER_PORT,
		ZoO_DEFAULT_IRC_SERVER_CHANNEL,
		ZoO_DEFAULT_IRC_USERNAME,
		ZoO_DEFAULT_IRC_REALNAME,
		ZoO_DEFAULT_REPLY_RATE
	);
}

int parse_string_arg(string* dest, const int i, const string[] args) {
	if (i == args.length) {
		criticalf("Missing value for parameter '%s'.", args[i - 1]);

		return -1;
	}

	*dest = args[i];

	return 0;
}


int parse_integer_arg(int* dest, const int i, const string[] args, const int min_val, const int max_val) {
	long result;
	char * endptr;
	const int old_errno = errno;

	if (i == args.length) {
		criticalf("Missing value for parameter '%s'.", args[i - 1]);

		return -1;
	}

	errno = 0;

	result = strtol(cast(char*)args[i].toStringz, &endptr, 10);

	if ((errno != 0) || ((*endptr) == '\n') || (result < min_val) || (result > max_val)) {
		criticalf("Invalid or missing value for parameter '%s', accepted range is [%d, %d] (integer).", args[i - 1], min_val, max_val);

		errno = old_errno;

		return -1;
	}

	*dest = cast(int) result;

	errno = old_errno;

	return 0;
}

int ZoO_parameters_initialize(ref ZoO_parameters param, const string[] args) {
	int i;

	load_default_parameters(param);

	for (i = 1; i < args.length; ++i) {
		if ((args[i] == "--data-filename") || (args[i] == "-df")) {
			i += 1;

			if (parse_string_arg(&(param.data_filename), i, args) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--new-data-filename") || (args[i] == "-ndf")) {
			i += 1;

			if (parse_string_arg(&(param.new_data_filename), i, args) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--irc-server-addr") || (args[i] == "-isa")) {
			i += 1;

			if (parse_string_arg(&(param.irc_server_addr), i, args) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--irc-server-port") || (args[i] == "-isp")) {
			i += 1;

			if (parse_string_arg(&(param.irc_server_port), i, args) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--irc-server-channel") || (args[i] == "-isc")) {
			i += 1;

			if (parse_string_arg(&(param.irc_server_channel), i, args) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--irc-username") || (args[i] == "-iu")) {
			i += 1;

			if (parse_string_arg(&(param.irc_username), i, args ) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--irc-realname") || (args[i] == "-in")) {
			i += 1;

			if (parse_string_arg(&(param.irc_realname), i, args) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--reply-rate") || (args[i] == "-rr")) {
			i += 1;

			if (parse_integer_arg(&(param.reply_rate), i, args, 0, 100) < 0) {
				return -1;
			}
		}
		else if ((args[i] == "--help") || (args[i] == "-h")) {
			print_help(args[0]);

			return 0;
		}
		else {
			break;
		}
	}

	if (i == args.length) {
		critical("Missing argument: NICKNAME");

		print_help(args[0]);

		return -1;
	}

	param.aliases = args[i..$];

	if (param.new_data_filename == null) {
		param.new_data_filename = param.data_filename;
	}

	return 1;
}

unittest {
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--data-filename", "hello", "testnickname"]);
		assert(parms.data_filename == "hello");
		assert(parms.new_data_filename == "hello");
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--new-data-filename", "hello", "testnickname"]);
		assert(parms.new_data_filename == "hello");
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--irc-server-addr", "example.com", "testnickname"]);
		assert(parms.irc_server_addr == "example.com");
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--irc-server-port", "420", "testnickname"]);
		assert(parms.irc_server_port == "420");
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--irc-server-channel", "#testchan", "testnickname"]);
		assert(parms.irc_server_channel == "#testchan");
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--irc-realname", "testname", "testnickname"]);
		assert(parms.irc_realname == "testname");
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--irc-username", "hello", "testnickname"]);
		assert(parms.irc_username == "hello");
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "--reply-rate", "50", "testnickname"]);
		assert(parms.reply_rate == 50);
		assert(parms.aliases[0] == "testnickname");
	}
	{
		auto parms = ZoO_parameters();
		ZoO_parameters_initialize(parms, ["testexec", "testnickname", "testalias1", "testalias2"]);
		assert(parms.aliases[0] == "testnickname");
		assert(parms.aliases[1] == "testalias1");
		assert(parms.aliases[2] == "testalias2");
	}
}
