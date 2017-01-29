#ifndef _ZoO_PIPE_PIPE_TYPES_H_
#define _ZoO_PIPE_PIPE_TYPES_H_

#include <stdio.h>

struct ZoO_pipe
{
   FILE * out;
   FILE * in;
};

struct ZoO_pipe_names
{
   char request_pipe[255];
   char reply_pipe[255];
};
//   const struct ZoO_pipe io [const restrict static 1]

#endif
