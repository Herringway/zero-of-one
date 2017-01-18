#ifndef _ZoO_IO_PARAMETERS_TYPES_H_
#define _ZoO_IO_PARAMETERS_TYPES_H_

#include "../pervasive.h"

/******************************************************************************/
/** DEFAULT VALUES ************************************************************/
/******************************************************************************/

#ifndef ZoO_DEFAULT_DATA_FILENAME
   #define ZoO_DEFAULT_DATA_FILENAME      "./memory.txt"
#endif

#ifndef ZoO_DEFAULT_IRC_SERVER_ADDR
   #define ZoO_DEFAULT_IRC_SERVER_ADDR    "irc.foonetic.net"
#endif

#ifndef ZoO_DEFAULT_IRC_SERVER_PORT
   #define ZoO_DEFAULT_IRC_SERVER_PORT    "6667"
#endif

#ifndef ZoO_DEFAULT_IRC_SERVER_CHANNEL
   #define ZoO_DEFAULT_IRC_SERVER_CHANNEL "#theborghivemind"
#endif

#ifndef ZoO_DEFAULT_IRC_USERNAME
   #define ZoO_DEFAULT_IRC_USERNAME       "zeroofone"
#endif

#ifndef ZoO_DEFAULT_IRC_REALNAME
   #define ZoO_DEFAULT_IRC_REALNAME       "Zero of One (bot)"
#endif

#ifndef ZoO_DEFAULT_REPLY_RATE
   #define ZoO_DEFAULT_REPLY_RATE         8
#endif

/******************************************************************************/
/** DEBUG LEVELS **************************************************************/
/******************************************************************************/

#ifndef ZoO_DEBUG_PARAMETERS
   #define ZoO_DEBUG_PARAMETERS (0 || ZoO_DEBUG_ALL)
#endif

/******************************************************************************/
/** FUNCTIONS *****************************************************************/
/******************************************************************************/

struct ZoO_parameters
{
   const char * restrict data_filename;
   const char * restrict new_data_filename;

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
