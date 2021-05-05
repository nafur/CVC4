/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Contains code for handling command-line options.
 *
 * For each <module>_options.toml configuration file, mkoptions.py
 * expands this template and generates a <module>_options.h file.
 */

#include "cvc5_private.h"

#ifndef CVC5__OPTIONS__${id}$_H
#define CVC5__OPTIONS__${id}$_H

#include "options/options.h"

#include <iostream>

// clang-format off
${includes}$

namespace cvc5::options {

${modes}$

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct Holder${id}$ {
${holder_spec}$
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

${option_names}$

${inls}$

}  // namespace cvc5::options

#endif /* CVC5__OPTIONS__${id}$_H */
//clang-format on
