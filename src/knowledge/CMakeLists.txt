set(
   SRC_FILES ${SRC_FILES}
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_finalize.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_get_random_sequence.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_get_random_target.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_learn_markov_sequence.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_learn_sequence.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_learn_word.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_search.c
   ${CMAKE_CURRENT_SOURCE_DIR}/knowledge_swt_tws_modifications.c
)

set(SRC_FILES ${SRC_FILES} PARENT_SCOPE)

