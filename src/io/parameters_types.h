#ifndef _ZoO_IO_PARAMETERS_TYPES_H_
#define _ZoO_IO_PARAMETERS_TYPES_H_

struct ZoO_parameters
{
   const char * restrict data_filename;

   const char * restrict irc_server_addr;
   const char * restrict irc_server_port;
   const char * restrict irc_server_channel;
   const char * restrict irc_username;
   const char * restrict irc_realname;

   int reply_rate;

   int aliases_count;
   const char * restrict * restrict aliases;
};

#endif
