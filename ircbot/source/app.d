module app;

import core.stdc.signal;
import core.stdc.stdlib;
import core.stdc.string;
import core.stdc.time;

import std.string;
import std.experimental.logger;

import tool.strings;

import io.error;
import io.parameters;
import io.data_input;
import io.data_output;
import io.network;

import core.assimilate;
import core.create_sentences;
import core.knowledge;

import pervasive;

alias ssize_t = ptrdiff_t;

int run = 1;

void request_termination (const int signo) {
	if ((signo == SIGINT) || (signo == SIGTERM)) {
		run = 0;
	}
}

struct ZoO_state {
	ZoO_parameters param;
	ZoO_knowledge knowledge;
	ZoO_network network;

	int initialize(const string[] args) {
		trace(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One is initializing...");

		srand(cast(uint)time(null));

		if (knowledge.initialize() < 0) {
			return -1;
		}

		if (ZoO_parameters_initialize(param, args) < 1) {
			knowledge.finalize();

			return -1;
		}

		return 0;
	}

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

	int network_connect() {
		return network.connect(param.irc_server_addr, param.irc_server_port, param.irc_server_channel, param.irc_username, param.irc_realname, param.aliases[0]);
	}
}


int should_reply(ref ZoO_parameters param, ref ZoO_strings string_, out int should_learn) {
	ZoO_index i, j;

	for (i = 0; i < param.aliases.length; ++i) {
		if (param.aliases[i] == string_.words[0]) {
			should_learn = 0;

			return 1;
		}

		for (j = 1; j < string_.words.length; ++j) {
			if (param.aliases[i] == string_.words[j]) {
				should_learn = 1;

				return 1;
			}
		}
	}

	should_learn = 1;

	return (param.reply_rate >= (rand() % 100));
}

void handle_user_join(ref ZoO_state s, ref ZoO_strings string_) {
	ZoO_char[] line;
	ZoO_index loc;

	if (s.param.reply_rate < (rand() % 100)) {
		return;
	}

	if (string_.parse(s.network.msg, ZoO_knowledge_punctuation_chars) < 0) {
		trace(ZoO_DEBUG_PROGRAM_FLOW, "Could not dissect join username.");

		return;
	}

	if ((s.knowledge.find(string_.words[0], loc) < 0) || (s.knowledge.words[loc].backward_links.length <= 3) || (s.knowledge.words[loc].forward_links.length <= 3)) {
		if (ZoO_knowledge_extend(s.knowledge, null, null, line) == 0) {
			if (line[0] == ' ') {
				s.network.send(line[1..$]);
			} else {
				s.network.send(line);
			}

		}
	} else {
		if (ZoO_knowledge_extend(s.knowledge, &string_, null, line) == 0) {
			if (line[0] == ' ') {
				s.network.send(line[1..$]);
			} else {
				s.network.send(line);
			}
		}
	}
}

void handle_message(ref ZoO_state s, ref ZoO_strings string_) {
	ZoO_char[] line;
	int reply, learn;

	if (string_.parse(s.network.msg, ZoO_knowledge_punctuation_chars) < 0) {
		trace(ZoO_DEBUG_PROGRAM_FLOW, "Could not dissect msg.");

		return;
	}

	if (string_.words.length == 0) {
		return;
	}

	reply = should_reply(s.param, string_, learn);

	if (learn) {
		/*
		* It would be best to do that after replying, but by then we no longer
		* have the string in 's.network.in'.
		*/
		ZoO_data_output_write_line(s.param.new_data_filename, s.network.msg.idup);
	}

	if (reply && (ZoO_knowledge_extend(s.knowledge, &string_, s.param.aliases, line) == 0)) {
		if (line[0] == ' ') {
			s.network.send(line[1..$]);
		} else {
			s.network.send(line);
		}
	}

	if (learn) {
		ZoO_knowledge_assimilate(s.knowledge, string_, s.param.aliases	);
	}
}

int main_loop(ref ZoO_state s) {
	ZoO_strings string_;
	ssize_t msg_offset, msg_size;
	ZoO_msg_type msg_type;

	msg_offset = 0;
	msg_size = 0;

	while (run) {
		if (s.network.receive(msg_type) == 0) {
			switch (msg_type) {
				case ZoO_msg_type.JOIN:
					handle_user_join(s, string_);
					break;

				case ZoO_msg_type.PRIVMSG:
					handle_message(s, string_);
					break;
				default: assert(0);
			}
		}
	}

	s.network.disconnect();

	return 0;
}

int main(string[] args) {
	ZoO_state s;

	if (s.initialize(args) < 0) {
		return -1;
	}

	if (s.load_data_file() < 0) {
		goto CRASH;
	}

	if (s.network_connect() < 0) {
		goto CRASH;
	}

	if (main_loop(s) < 0) {
		goto CRASH;
	}

	trace(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One terminated normally.");

	return 0;

	CRASH:
	{
		trace(ZoO_DEBUG_PROGRAM_FLOW, "Zero of One terminated by crashing.");

		return -1;
	}
}