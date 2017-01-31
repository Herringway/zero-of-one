#ifndef _ZoO_PIPE_PIPE_TYPES_H_
#define _ZoO_PIPE_PIPE_TYPES_H_

#define ZoO_PIPE_NAME_LENGTH 255

#include <stdio.h>

struct ZoO_pipe
{
   FILE * out;
   FILE * in;
};

struct ZoO_pipe_names
{
   char request_pipe[ZoO_PIPE_NAME_LENGTH];
   char reply_pipe[ZoO_PIPE_NAME_LENGTH];
};
//   const struct ZoO_pipe io [const restrict static 1]

#endif
