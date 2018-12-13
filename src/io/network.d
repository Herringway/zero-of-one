module io.network;

import core.time;
import core.thread;
import std.format;
import std.socket;
import std.string;
import std.experimental.logger;

import io.error;

import pervasive;

import core.stdc.string : memmove;

enum ZoO_msg_type {
	PRIVMSG,
	JOIN
}

struct ZoO_network {
	private size_t buffer_index;
	private size_t buffer_remaining;
	AddressInfo[] addrInfo;
	private ZoO_char[513] buffer;
	private ZoO_char[] in_;
	private ZoO_char[] out_;
	char[] msg;
	Socket socket;
	string channel;
	string user;
	string name;
	string nick;
	int re_create_socket() {
		if ((socket !is null) && socket.isAlive) {
			socket.close();
		}

		socket = new Socket(addrInfo[0]);
		socket.setOption(SocketOptionLevel.SOCKET, SocketOption.RCVTIMEO, ZoO_NETWORK_TIMEOUT);
		socket.setOption(SocketOptionLevel.SOCKET, SocketOption.SNDTIMEO, ZoO_NETWORK_TIMEOUT);

		trace(ZoO_DEBUG_NETWORK, "(Re)connecting to network...");

		socket.connect(addrInfo[0].address);

		return 0;
	}

	int reconnect() {
		buffer = 0;

		buffer_index = 0;
		buffer_remaining = 0;

		if (re_create_socket() < 0) {
			return -1;
		}

		out_ = format!"USER %s 8 *:%s\r\n"(user, name).dup;

		if (socket.send(out_) < 1) {
			goto RETURN_WRITE_FAILED;
		}

		out_ = format!"NICK %s\r\n"(nick).dup;

		if (socket.send(out_) < 1) {
			goto RETURN_WRITE_FAILED;
		}

		buffer_remaining = 0;
		buffer_index = 0;

		trace(ZoO_DEBUG_NETWORK, "(Re)connected.");

		return 0;

	RETURN_WRITE_FAILED:
		errorf("Unable to write to the network: %s", lastSocketError);

		return -1;
	}

	int connect(string host, string port, string channel, string user, string name, string nick) {
		this.channel = channel;
		this.user = user;
		this.name = name;
		this.nick = nick;
		buffer_index = 0;
		buffer_remaining = 0;
		buffer = 0;

		addrInfo = getAddressInfo(host, port, AddressFamily.INET, SocketType.STREAM);

		return reconnect();
	}

	void buffer_msg() {
		ptrdiff_t in_count, i;

		if (buffer_remaining > 0) {
			in_count = buffer_remaining;
			buffer_remaining = 0;

			goto PARSE_READ;
		}

	READ_MORE:
		in_count = socket.receive(buffer);

		if (in_count <= 0) {
			errorf("Could not read from network: %s", lastSocketError);

			while (reconnect() < 0) {
				trace(ZoO_DEBUG_NETWORK, "Attempting new connection in 5s.");
				Thread.sleep(ZoO_NETWORK_RECONNECT_WAIT);
			}

			goto READ_MORE;
		}

	PARSE_READ:
		if (buffer_index == 0) {
			in_ = new char[](513);
		}
		for (i = 0; i < in_count; ++i) {
			in_[buffer_index] = buffer[i];

			if ((buffer_index > 0) && (in_[buffer_index - 1] == '\r') && (in_[buffer_index] == '\n')) {
				buffer_remaining = (in_count - (i + 1));
				in_ = in_[0..buffer_index];
				buffer_index = 0;
				if (buffer_remaining > 0) {
					memmove(buffer.ptr, buffer.ptr + (i + 1), buffer_remaining);
				}

				return;
			}

			buffer_index += 1;

			if (buffer_index > 512) {
				warning("Incoming message is too long. Discarded.");

				buffer_index = 0;
				buffer_remaining = 0;

				break;
			}
		}

		goto READ_MORE;
	}


	void handle_ping() {
		static if (ZoO_RANDOMLY_IGNORE_PING == 1) {
			if ((rand() % 10) < 3) {
				trace(ZoO_DEBUG_NETWORK, "Ping request ignored.");

				return;
			}

		}

		tracef(ZoO_DEBUG_NETWORK_PING, "[NET.in] %s", in_);

		in_[1] = 'O';

		if (socket.send(in_) < 1) {
			errorf("Could not reply to PING request: %s", lastSocketError);

			while (reconnect() < 0) {
				trace(ZoO_DEBUG_NETWORK, "Attempting new connection in 5s.");
				Thread.sleep(ZoO_NETWORK_RECONNECT_WAIT);
			}

			return;
		}

		tracef(ZoO_DEBUG_NETWORK_PING, "[NET.out] %s", in_);

	}

	int receive(out ZoO_msg_type type) {
		ptrdiff_t cmd, i;
		ptrdiff_t msg_offset, msg_size;

	READ_NEW_MSG:
		buffer_msg();

		if (in_[0..4] == "PING") {

			handle_ping();

			goto READ_NEW_MSG;
		}

		if (in_.length == 0) {
			goto READ_NEW_MSG;
		}

		tracef(ZoO_DEBUG_NETWORK, "[NET.in] %s", in_);

		if (in_[0] == ':') {
			cmd = 0;

			for (i = 1; i < 512; i++) {
				if (in_[i] == ' ') {
					cmd = (i + 1);

					break;
				}
			}

			if (in_[cmd..cmd+3] == "001") {
				out_ = format!"JOIN :%s\r\n"(channel).dup;

				if (socket.send(out_) < 1) {
					errorf("Could not send JOIN request: %s", lastSocketError);

					if (reconnect() < 0) {
						return -1;
					}
				}

				tracef(ZoO_DEBUG_NETWORK, "[NET.out] %s", out_[0..$-2]);

				goto READ_NEW_MSG;
			}

			if (in_[cmd..cmd+4] == "JOIN") {
				for (i = 1; (i < 512) && (in_[i] != '!'); ++i) {}

				if ((i == 512) || (i == 1)) {
					errorf("Could not find JOIN username: %s", in_);

					goto READ_NEW_MSG;
				}

				msg_offset = 1;
				msg_size = (i - 1);
				msg = in_[msg_offset..msg_offset+msg_size];

				type = ZoO_msg_type.JOIN;

				return 0;
			}

			if (in_[cmd..cmd+7] == "PRIVMSG") {

				for (; i < 512; i++) {
					if (in_[i] == ':') {
						cmd = (i + 1);

						break;
					}
				}

				msg_offset = cmd;
				msg_size = in_.length - cmd - 1;
				msg = in_[msg_offset..msg_offset+msg_size];

				type = ZoO_msg_type.PRIVMSG;

				return 0;
			}
		}

		if (in_[cmd..cmd+5] == "ERROR") {
			while (reconnect() < 0) {
				trace(ZoO_DEBUG_NETWORK, "Attempting new connection in 5s.");
				Thread.sleep(ZoO_NETWORK_RECONNECT_WAIT);
			}
		}

		goto READ_NEW_MSG;
	}

	int send(char[] line) {
		string str;

		if (line[0..7] == "\001action") {

			line[1] = 'A';
			line[2] = 'C';
			line[3] = 'T';
			line[4] = 'I';
			line[5] = 'O';
			line[6] = 'N';

			str = format!"PRIVMSG %s :%s\001\r\n"(channel, line);
		} else {
			str = format!"PRIVMSG %s :%s\r\n"(channel, line);
		}

		if (socket.send(str) < 1) {
			errorf("Could not send PRIVMSG: %s.", lastSocketError);

			if (reconnect() < 0) {
				return -2;
			} else {
				return -1;
			}
		}

		tracef(ZoO_DEBUG_NETWORK, "[NET.out] %s", in_[0..$-2]);

		return 0;
	}

	void disconnect() {
		socket.shutdown(SocketShutdown.BOTH);
		socket.close();
	}
}

