/*********************                                                        */
/*! \file memory_mapped_input_buffer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ANTLR input buffer from a memory-mapped file.
 **
 ** ANTLR input buffer from a memory-mapped file.
 **/

#include "cvc4parser_private.h"

#ifndef CVC5__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H
#define CVC5__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H

#include <antlr3input.h>
#include <string>

namespace cvc5 {
namespace parser {

#ifdef __cplusplus
extern "C" {
#endif

pANTLR3_INPUT_STREAM
MemoryMappedInputBufferNew(const std::string& filename);

#ifdef __cplusplus
}/* extern "C" */
#endif

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H */
