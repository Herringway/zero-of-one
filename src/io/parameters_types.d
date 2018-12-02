module io.parameters_types;

struct ZoO_parameters
{
   const(char)* data_filename;
   const(char)* new_data_filename;

   const(char)* irc_server_addr;
   const(char)* irc_server_port;
   const(char)* irc_server_channel;
   const(char)* irc_username;
   const(char)* irc_realname;

   int reply_rate;

   int aliases_count;
   const(char*)* aliases;
}
