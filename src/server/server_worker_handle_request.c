#include "../pervasive.h"

#include "../error/error.h"

#include "../sequence/sequence.h"

#include "../knowledge/knowledge.h"

#include "../parameters/parameters.h"

#include "../storage/storage.h"

#include "server.h"

static int load_reply
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   ZoO_index rarest_word_id;

   if
   (
      ZoO_knowledge_lock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      ) < 0
   )
   {
      return -1;
   }

   if
   (
      ZoO_knowledge_rarest_word
      (
         worker->params.knowledge,
         worker->sequence_buffer,
         worker->sequence_buffer_length,
         &rarest_word_id
      ) < 0
   )
   {
      ZoO_S_ERROR(worker->socket_as_file, "Could not find rarest word.");

      ZoO_knowledge_unlock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      );

      return -1;
   }

   ZoO_knowledge_unlock_access
   (
      worker->params.knowledge,
      worker->socket_as_file
   );

   ZoO_DEBUG
   (
      worker->socket_as_file,
      1,
      "Word selected as pillar: %u",
      rarest_word_id
   );

   if
   (
      ZoO_sequence_create_from
      (
         rarest_word_id,
         (size_t *) NULL,
         worker->params.knowledge,
         ZoO_parameters_get_markov_order(worker->params.server_params),
			&(worker->sequence_buffer),
			&(worker->sequence_buffer_capacity),
			&(worker->sequence_buffer_length),
			worker->socket_as_file
      ) < 0
   )
   {
      ZoO_S_ERROR(worker->socket_as_file, "Could not create reply from selected word.");

      return -1;
   }

   if
   (
      ZoO_sequence_to_undercase_string
      (
	   	worker->sequence_buffer,
	   	worker->sequence_buffer_length,
         worker->params.knowledge,
			&(worker->buffer),
			&(worker->buffer_capacity),
			&(worker->buffer_length),
			worker->socket_as_file
      ) < 0
   )
   {
      ZoO_S_ERROR(worker->socket_as_file, "Could not convert reply sequence to string.");

      return -1;
   }

   return 0;
}

static int handle_rpv
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   /* TODO */

   return -1;
}

static int handle_rl
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   if
   (
      ZoO_sequence_from_undercase_string
		(
			(const ZoO_char *) (worker->buffer + 4),
			(worker->buffer_length - 5),
			worker->params.knowledge,
			&(worker->sequence_buffer),
			&(worker->sequence_buffer_capacity),
			&(worker->sequence_buffer_length),
			worker->socket_as_file
		) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if
   (
      ZoO_knowledge_lock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      ) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if
   (
      ZoO_knowledge_learn_sequence
      (
         worker->params.knowledge,
         worker->sequence_buffer,
         worker->sequence_buffer_length,
         ZoO_parameters_get_markov_order(worker->params.server_params),
         worker->socket_as_file
      ) < 0
   )
   {
      ZoO_knowledge_unlock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      );

      return ZoO_server_worker_send_negative(worker);
   }

   ZoO_knowledge_unlock_access
   (
      worker->params.knowledge,
      worker->socket_as_file
   );

   return ZoO_server_worker_send_positive(worker);
}

static int handle_rls
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   if
   (
      ZoO_sequence_from_undercase_string
		(
			(const ZoO_char *) (worker->buffer + 5),
			(worker->buffer_length - 6),
			worker->params.knowledge,
			&(worker->sequence_buffer),
			&(worker->sequence_buffer_capacity),
			&(worker->sequence_buffer_length),
			worker->socket_as_file
		) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if
   (
      ZoO_knowledge_lock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      ) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if
   (
      ZoO_knowledge_learn_sequence
      (
         worker->params.knowledge,
         worker->sequence_buffer,
         worker->sequence_buffer_length,
         ZoO_parameters_get_markov_order(worker->params.server_params),
         worker->socket_as_file
      ) < 0
   )
   {
      ZoO_knowledge_unlock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      );

      return ZoO_server_worker_send_negative(worker);
   }

   ZoO_knowledge_unlock_access
   (
      worker->params.knowledge,
      worker->socket_as_file
   );

   if
   (
      ZoO_storage_write_line
      (
         ZoO_parameters_get_storage_filename(worker->params.server_params),
         (worker->buffer + 5),
         (worker->buffer_length - 5), /* Keep the \n this time. */
         worker->socket_as_file
      ) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   return ZoO_server_worker_send_positive(worker);
}

static int handle_rlsr
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   if
   (
      ZoO_sequence_from_undercase_string
		(
			(const ZoO_char *) (worker->buffer + 6),
			(worker->buffer_length - 7),
			worker->params.knowledge,
			&(worker->sequence_buffer),
			&(worker->sequence_buffer_capacity),
			&(worker->sequence_buffer_length),
			worker->socket_as_file
		) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if
   (
      ZoO_knowledge_lock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      ) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if
   (
      ZoO_knowledge_learn_sequence
      (
         worker->params.knowledge,
         worker->sequence_buffer,
         worker->sequence_buffer_length,
         ZoO_parameters_get_markov_order(worker->params.server_params),
         worker->socket_as_file
      ) < 0
   )
   {
      ZoO_knowledge_unlock_access
      (
         worker->params.knowledge,
         worker->socket_as_file
      );

      return ZoO_server_worker_send_negative(worker);
   }

   ZoO_knowledge_unlock_access
   (
      worker->params.knowledge,
      worker->socket_as_file
   );

   if
   (
      ZoO_storage_write_line
      (
         ZoO_parameters_get_storage_filename(worker->params.server_params),
         (worker->buffer + 6),
         (worker->buffer_length - 6), /* Keep the \n this time. */
         worker->socket_as_file
      ) < 0
   )
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if (load_reply(worker) < 0)
   {
      return ZoO_server_worker_send_negative(worker);
   }

   if (ZoO_server_worker_send_generated_reply(worker) < 0)
   {
      return -1;
   }

   return ZoO_server_worker_send_positive(worker);
}

static int handle_rr
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   if
   (
      ZoO_sequence_from_undercase_string
		(
			(const ZoO_char *) (worker->buffer + 4),
			(worker->buffer_length - 5),
			worker->params.knowledge,
			&(worker->sequence_buffer),
			&(worker->sequence_buffer_capacity),
			&(worker->sequence_buffer_length),
			worker->socket_as_file
		) < 0
   )
   {
      ZoO_S_DEBUG(worker->socket_as_file, 1, "?RR failed at string to sequence.");

      return ZoO_server_worker_send_negative(worker);
   }

   if (load_reply(worker) < 0)
   {
      ZoO_S_DEBUG(worker->socket_as_file, 1, "?RR failed at load reply.");
      return ZoO_server_worker_send_negative(worker);
   }

   if (ZoO_server_worker_send_generated_reply(worker) < 0)
   {
      return -1;
   }

   return ZoO_server_worker_send_positive(worker);
}

int ZoO_server_worker_handle_request
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   if (ZoO_IS_PREFIX("?RPV ", worker->buffer))
   {
      return handle_rpv(worker);
   }
   else if (ZoO_IS_PREFIX("?RL ", worker->buffer))
   {
      return handle_rl(worker);
   }
   else if (ZoO_IS_PREFIX("?RLS ", worker->buffer))
   {
      return handle_rls(worker);
   }
   else if (ZoO_IS_PREFIX("?RLSR ", worker->buffer))
   {
      return handle_rlsr(worker);
   }
   else if (ZoO_IS_PREFIX("?RR ", worker->buffer))
   {
      return handle_rr(worker);
   }
   else
   {
      ZoO_S_ERROR(worker->socket_as_file, "Unsupported request received.");

      return ZoO_server_worker_send_negative(worker);
   }

   return 0;
}
