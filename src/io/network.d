module io.network;

import std.format;
import std.string;
import std.experimental.logger;

import io.error;

import pervasive;

import core.stdc.errno : errno;
import core.stdc.string : strerror, memset, memmove;

import core.sys.posix.sys.time : timeval;
import core.sys.posix.unistd : ssize_t, read, sleep, write, close;
static import core.sys.posix.netdb;
import core.sys.posix.netdb : getaddrinfo, freeaddrinfo, AF_INET, SOCK_STREAM, EAI_SYSTEM, setsockopt, socket, SOL_SOCKET, SO_RCVTIMEO, SO_SNDTIMEO, gai_strerror;

enum ZoO_msg_type {
	PRIVMSG,
	JOIN
}

struct ZoO_network {
	size_t buffer_index;
	size_t buffer_remaining;
	core.sys.posix.netdb.addrinfo* addrinfo;
	ZoO_char[513] buffer;
	ZoO_char[] in_;
	ZoO_char[] out_;
	int connection;
	string channel;
	string user;
	string name;
	string nick;
	int re_create_socket() {
		timeval timeout;
		const int old_errno = errno;

		errno = 0;
		timeout.tv_sec = ZoO_NETWORK_TIMEOUT;
		timeout.tv_usec = 0;

		if (connection != -1) {
			close(connection);
		}

		connection = socket(addrinfo.ai_family, addrinfo.ai_socktype, addrinfo.ai_protocol);

		if (connection == -1) {
			error("Could not create socket: %s.", strerror(errno));

			goto RETURN_FAILED;
		}

		if ((setsockopt(connection, SOL_SOCKET, SO_RCVTIMEO, &timeout, timeval.sizeof) < 0) || (setsockopt(connection, SOL_SOCKET, SO_SNDTIMEO, &timeout, timeval.sizeof) < 0)) {
			error("Could not set timeout on network socket: %s", strerror(errno));

			goto RETURN_FAILED;
		}

		trace(ZoO_DEBUG_NETWORK, "(Re)connecting to network...");

		if (core.sys.posix.netdb.connect(connection, addrinfo.ai_addr, addrinfo.ai_addrlen) != 0) {
			error("Could not establish connection: %s", strerror(errno));

			goto RETURN_FAILED;
		}

		errno = old_errno;

		return 0;

	RETURN_FAILED:
		errno = old_errno;

		return -1;
	}

	int reconnect() {
		const int old_errno = errno;

		buffer = 0;

		buffer_index = 0;
		buffer_remaining = 0;

		if (re_create_socket() < 0) {
			return -1;
		}

		out_ = format!"USER %s 8 *:%s\r\n"(user, name).dup;

		if (write(connection, out_.ptr, out_.length) < 1) {
			goto RETURN_WRITE_FAILED;
		}

		out_ = format!"NICK %s\r\n"(nick).dup;

		if (write(connection, out_.ptr, out_.length) < 1) {
			goto RETURN_WRITE_FAILED;
		}

		buffer_remaining = 0;
		buffer_index = 0;

		trace(ZoO_DEBUG_NETWORK, "(Re)connected.");

		errno = old_errno;

		return 0;

	RETURN_WRITE_FAILED:
		error("Unable to write to the network: %s", strerror(errno).fromStringz);

		errno = old_errno;

		return -1;
	}

	int connect(string host, string port, string channel, string user, string name, string nick) {
		int errorCode;
		core.sys.posix.netdb.addrinfo hints;
		const int old_errno = errno;

		connection = -1;
		this.channel = channel;
		this.user = user;
		this.name = name;
		this.nick = nick;
		buffer_index = 0;
		buffer_remaining = 0;

		memset(&hints, 0, addrinfo.sizeof);
		buffer = 0;

		hints.ai_family = AF_INET;
		hints.ai_socktype = SOCK_STREAM;

		errno = 0;

		errorCode = getaddrinfo(host.toStringz, port.toStringz, &hints, &addrinfo);

		if (errorCode != 0) {
			if (errorCode == EAI_SYSTEM) {
				error("Could not retrieve server information: %s.", strerror(errno));
			} else {
				criticalf("Could not retrieve server information: %s.", gai_strerror(errorCode));
			}

			errno = old_errno;

			return -1;
		}

		errno = old_errno;

		reconnect();

		return 0;
	}

	void buffer_msg() {
		ssize_t in_count, i;

		if (buffer_remaining > 0) {
			in_count = buffer_remaining;
			buffer_remaining = 0;

			goto PARSE_READ;
		}

	READ_MORE:
		in_count = read(connection, buffer.ptr, 512);

		if (in_count <= 0) {
			error("Could not read from network: %s", strerror(errno).fromStringz);

			while (reconnect() < 0) {
				trace(ZoO_DEBUG_NETWORK, "Attempting new connection in 5s.");
				sleep(5);
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
		const int old_errno = errno;

		static if (ZoO_RANDOMLY_IGNORE_PING == 1) {
			if ((rand() % 10) < 3) {
				trace(ZoO_DEBUG_NETWORK, "Ping request ignored.");

				return;
			}

		}

		tracef(ZoO_DEBUG_NETWORK_PING, "[NET.in] %s", in_);

		in_[1] = 'O';

		errno = 0;

		if (write(connection, in_.ptr, in_.length) < 1) {
			error("Could not reply to PING request: %s", strerror(errno).fromStringz);

			errno = old_errno;

			while (reconnect() < 0) {
				trace(ZoO_DEBUG_NETWORK, "Attempting new connection in 5s.");
				sleep(5);
			}

			return;
		}

		errno = old_errno;

		tracef(ZoO_DEBUG_NETWORK_PING, "[NET.out] %s", in_);

	}

	int receive(out ssize_t msg_offset, out ssize_t msg_size, out ZoO_msg_type type) {
		const int old_errno = errno;
		ssize_t cmd, i;

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

				errno = 0;

				if (write(connection, out_.ptr, out_.length) < 1) {
					error("Could not send JOIN request: %s", strerror(errno));

					errno = old_errno;

					if (reconnect() < 0) {
						return -1;
					}
				}

				errno = old_errno;

				tracef(ZoO_DEBUG_NETWORK, "[NET.out] %s", out_[0..$-2]);

				goto READ_NEW_MSG;
			}

			if (in_[cmd..cmd+4] == "JOIN") {
				for (i = 1; (i < 512) && (in_[i] != '!'); ++i) {}

				if ((i == 512) || (i == 1)) {
					error("Could not find JOIN username: %s", in_);

					goto READ_NEW_MSG;
				}

				msg_offset = 1;
				msg_size = (i - 1);
				in_[i] = '\0';

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

				type = ZoO_msg_type.PRIVMSG;

				return 0;
			}
		}

		if (in_[cmd..cmd+5] == "ERROR") {
			while (reconnect() < 0) {
				trace(ZoO_DEBUG_NETWORK, "Attempting new connection in 5s.");
				sleep(5);
			}
		}

		goto READ_NEW_MSG;
	}

	int send() {
		const int old_errno = errno;

		if (out_[0..7] == "\001action") {

			out_[1] = 'A';
			out_[2] = 'C';
			out_[3] = 'T';
			out_[4] = 'I';
			out_[5] = 'O';
			out_[6] = 'N';

			in_ = format!"PRIVMSG %s :%s\001\r\n"(channel, out_).dup;
		} else {
			in_ = format!"PRIVMSG %s :%s\r\n"(channel, out_).dup;
		}

		errno = 0;

		if (write(connection, in_.ptr, in_.length) < 1) {
			error("Could not send PRIVMSG: %s.", strerror(errno));

			errno = old_errno;

			if (reconnect() < 0) {
				return -2;
			} else {
				return -1;
			}
		}

		errno = old_errno;

		tracef(ZoO_DEBUG_NETWORK, "[NET.out] %s", in_[0..$-2]);

		return 0;
	}

	void disconnect() {
		freeaddrinfo(addrinfo);
		close(connection);
	}
}

