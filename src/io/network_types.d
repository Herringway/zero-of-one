module io.network_types;

static import core.sys.posix.netdb;

import pervasive;

enum ZoO_msg_type {
	ZoO_PRIVMSG,
	ZoO_JOIN
}

struct ZoO_network {
	size_t buffer_index;
	size_t buffer_remaining;
	size_t in_length;
	core.sys.posix.netdb.addrinfo* addrinfo;
	ZoO_char[513] buffer;
	ZoO_char[513] in_;
	ZoO_char[513] out_;
	int connection;
	string channel;
	string user;
	string name;
	string nick;
}
