module io.parameters_types;

struct ZoO_parameters {
	string data_filename;
	string new_data_filename;

	string irc_server_addr;
	string irc_server_port;
	string irc_server_channel;
	string irc_username;
	string irc_realname;

	int reply_rate;

	const(string)[] aliases;
}
