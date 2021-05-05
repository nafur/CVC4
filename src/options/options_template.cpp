/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Andrew Reynolds
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
 */

#include <unistd.h>
#include <string.h>
#include <time.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iomanip>
#include <new>
#include <string>
#include <sstream>
#include <limits>

#include "base/check.h"
#include "base/exception.h"
#include "base/output.h"
#include "options/language.h"
#include "options/options_handler.h"
#include "options/options_listener.h"
#include "options/options_api.h"

// clang-format off
${headers_module}$

#include "base/cvc5config.h"

${headers_handler}$

using namespace cvc5;
using namespace cvc5::options;
// clang-format on

namespace cvc5 {

thread_local Options* Options::s_current = NULL;

Options::Options(OptionsListener* ol)
    : ${holder_mem_inits}$
      d_handler(new options::OptionsHandler(this)),
      d_olisten(ol)
{}

Options::~Options() {
  delete d_handler;
}

void Options::copyValues(const Options& options){
  if(this != &options) {
${holder_mem_copy}$
  }
}

void Options::setListener(OptionsListener* ol) { d_olisten = ol; }

// clang-format off

// clang-format on

}  // namespace cvc5
