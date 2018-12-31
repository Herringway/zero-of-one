module app;

import std.range;
import std.stdio;
import vibe.core.core;
import vibe.core.net;
import vibe.stream.operations;
import vibe.stream.stdio;
import vibe.stream.tls;
import vibe.stream.wrapper;
import virc;
import siryul;


struct Settings {
	string address;
	ushort port;
	bool tls;
	string nickname;
	string username;
	string realname;
	ubyte replyRate = 8;
	string memoryFile = "memory.txt";
	string[] aliases;
	string[] channels;
}

mixin template Client() {
	import tool.strings;

	import io.data_input;
	import io.data_output;

	import core.assimilate;
	import core.create_sentences;
	import core.knowledge;

	import pervasive;
	import std.stdio : writefln, writef;
	import std.format : format;
	ZoO_knowledge knowledge;
	string[] aliases;
	string[] channelsToJoin;
	ubyte replyRate;
	string memoryFile;
	void onMessage(const User user, const Target target, const Message msg, const MessageMetadata metadata) @safe {
		if (user.nickname == nickname) {
			return;
		}
		if (msg.isCTCP) {
			if (msg.ctcpCommand == "ACTION") {
				tryReply(target, format!"\001ACTION %s %s\001"(user.nickname, msg.ctcpArgs));
			} else if (msg.ctcpCommand == "VERSION") {
				ctcpReply(Target(user), "VERSION", "zero-of-one");
			}
		} else if (msg.isReplyable) {
			tryReply(target, msg.msg);
		}
	}

	void onJoin(const User user, const Channel channel, const MessageMetadata metadata) @safe {
		tryReply(Target(channel), user.nickname);
	}

	void onPart(const User user, const Channel channel, const string message, const MessageMetadata metadata) @safe {
		if (message == "") {
			tryReply(Target(channel), user.nickname);
		} else {
			tryReply(Target(channel), format!"%s has left (%s)"(user.nickname, message));
		}
	}

	void onKick(const User user, const Channel channel, const User initiator, const string message, const MessageMetadata metadata) @safe {
		tryReply(Target(channel), format!"%s was kicked by %s (%s)"(user.nickname, initiator, message));
	}

	void onTopic(const User user, const Channel channel, const string topic, const MessageMetadata metadata) @safe {
		tryReply(Target(channel), format!"%s changed topic to %s"(user.nickname, topic));
	}
	void tryReply(const Target target, const string message) @safe {
		writefln!"Attempting to learn/reply to %s for: %s"(target, message);
		ZoO_strings string_;

		string_.parse(message, ZoO_knowledge_punctuation_chars);

		if (string_.words.length == 0) {
			return;
		}

		auto howToProceed = shouldLearnAndReply(string_);

		if (howToProceed.reply) {
			auto line = ZoO_knowledge_extend(knowledge, string_, aliases, false);
			msg(target, Message(line));
		}

		if (howToProceed.learn) {
			ZoO_data_output_write_line(memoryFile, message);
			ZoO_knowledge_assimilate(knowledge, string_, aliases);
		}
	}

	auto shouldLearnAndReply(ref ZoO_strings str) @safe {
		import std.random : uniform;
		import std.typecons : tuple;
		foreach (alias_; aliases) {
			foreach (idx, word; str.words) {
				if (alias_ == word) {
					return tuple!("learn", "reply")(idx != 0, true);
				}
			}
		}
		return tuple!("learn", "reply")(true, replyRate >= uniform(0, 101));
	}

	void onConnect() @safe {
		foreach (channel; channelsToJoin) {
			join(channel);
		}
	}
	int load_data_file() @system {
		ZoO_data_input input;

		if (input.open(memoryFile) < 0) {
			return -1;
		}

		while (input.read_line(ZoO_knowledge_punctuation_chars) == 0) {
			ZoO_knowledge_assimilate(knowledge, input.str, aliases);
		}

		input.close();

		return 0;
	}
}

auto runClient(T)(Settings settings, ref T stream) {
	import std.typecons;
	auto output = refCounted(streamOutputRange(stream));
	auto client = ircClient!Client(output, NickInfo(settings.nickname, settings.username, settings.realname));
	client.channelsToJoin = settings.channels;
	client.aliases = settings.nickname~settings.aliases;
	client.replyRate = settings.replyRate;
	client.memoryFile = settings.memoryFile;

	void readIRC() {
		while(!stream.empty) {
			put(client, stream.readLine().idup);
		}
	}
	runTask(&readIRC);
	return runApplication();
}

int main() {
	import std.file : exists, readText;
	import std.json : JSON_TYPE, parseJSON;
	if (!exists("settings.yml")) {
		toFile!YAML(Settings(), "settings.yml");
		stderr.writeln("Please edit settings.yml");
		return -1;
	}
	auto settings = fromFile!(Settings, YAML)("settings.yml");
	auto conn = connectTCP(settings.address, settings.port);
	Stream stream;
	if (settings.tls) {
		auto sslctx = createTLSContext(TLSContextKind.client);
		sslctx.peerValidationMode = TLSPeerValidationMode.none;
		try {
			stream = createTLSStream(conn, sslctx);
		} catch (Exception) {
			writeln("SSL connection failed!");
			return 1;
		}
		return runClient(settings, stream);
	} else {
		return runClient(settings, conn);
	}
}