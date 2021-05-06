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

#include "base/cvc5config.h"
#include "options/options_handler.h"
#include "options/options_listener.h"

// clang-format off
${headers_module}$
// clang-format on

namespace cvc5
{
  thread_local Options* Options::s_current = nullptr;

  Options::Options(OptionsListener * ol)
      :
// clang-format off
${holder_mem_inits}$
// clang-format on
        d_olisten(ol),
        d_handler(std::make_unique<options::OptionsHandler>(this))
  {
  }

  Options::~Options() {}

  void Options::copyValues(const Options& options)
  {
    if (this != &options)
    {
// clang-format off
${holder_mem_copy}$
// clang-format on
    }
  }

${holder_getter_impl}$

  void Options::setListener(OptionsListener * ol) { d_olisten = ol; }

  void Options::notifyListener(const std::string& key)
  {
    if (d_olisten != nullptr)
    {
      d_olisten->notifySetOption(key);
    }
  }

}  // namespace cvc5
