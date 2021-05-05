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
#include "options/base_handlers.h"

${headers_handler}$

using namespace cvc5;
using namespace cvc5::options;
// clang-format on

namespace cvc5 {

thread_local Options* Options::s_current = NULL;

/**
 * This is a default handler for options of built-in C++ type.  This
 * template is really just a helper for the handleOption() template,
 * below.  Variants of this template handle numeric and non-numeric,
 * integral and non-integral, signed and unsigned C++ types.
 * handleOption() makes sure to instantiate the right one.
 *
 * This implements default behavior when e.g. an option is
 * unsigned but the user specifies a negative argument; etc.
 */
template <class T, bool is_numeric, bool is_integer>
struct OptionHandler {
  static T handle(std::string option, std::string optionarg);
};/* struct OptionHandler<> */

/** Variant for integral C++ types */
template <class T>
struct OptionHandler<T, true, true> {
  static bool stringToInt(T& t, const std::string& str) {
    std::istringstream ss(str);
    ss >> t;
    char tmp;
    return !(ss.fail() || ss.get(tmp));
  }

  static bool containsMinus(const std::string& str) {
    return str.find('-') != std::string::npos;
  }

  static T handle(const std::string& option, const std::string& optionarg) {
    try {
      T i;
      bool success = stringToInt(i, optionarg);

      if(!success){
        throw OptionException(option + ": failed to parse "+ optionarg +
                              " as an integer of the appropriate type.");
      }

      // Depending in the platform unsigned numbers with '-' signs may parse.
      // Reject these by looking for any minus if it is not signed.
      if( (! std::numeric_limits<T>::is_signed) && containsMinus(optionarg) ) {
        // unsigned type but user gave negative argument
        throw OptionException(option + " requires a nonnegative argument");
      } else if(i < std::numeric_limits<T>::min()) {
        // negative overflow for type
        std::stringstream ss;
        ss << option << " requires an argument >= "
           << std::numeric_limits<T>::min();
        throw OptionException(ss.str());
      } else if(i > std::numeric_limits<T>::max()) {
        // positive overflow for type
        std::stringstream ss;
        ss << option << " requires an argument <= "
           << std::numeric_limits<T>::max();
        throw OptionException(ss.str());
      }

      return i;

      // if(std::numeric_limits<T>::is_signed) {
      //   return T(i.getLong());
      // } else {
      //   return T(i.getUnsignedLong());
      // }
    } catch(std::invalid_argument&) {
      // user gave something other than an integer
      throw OptionException(option + " requires an integer argument");
    }
  }
};/* struct OptionHandler<T, true, true> */

/** Variant for numeric but non-integral C++ types */
template <class T>
struct OptionHandler<T, true, false> {
  static T handle(std::string option, std::string optionarg) {
    std::stringstream in(optionarg);
    long double r;
    in >> r;
    if(! in.eof()) {
      // we didn't consume the whole string (junk at end)
      throw OptionException(option + " requires a numeric argument");
    }

    if(! std::numeric_limits<T>::is_signed && r < 0.0) {
      // unsigned type but user gave negative value
      throw OptionException(option + " requires a nonnegative argument");
    } else if(r < -std::numeric_limits<T>::max()) {
      // negative overflow for type
      std::stringstream ss;
      ss << option << " requires an argument >= "
         << -std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    } else if(r > std::numeric_limits<T>::max()) {
      // positive overflow for type
      std::stringstream ss;
      ss << option << " requires an argument <= "
         << std::numeric_limits<T>::max();
      throw OptionException(ss.str());
    }

    return T(r);
  }
};/* struct OptionHandler<T, true, false> */

/** Variant for non-numeric C++ types */
template <class T>
struct OptionHandler<T, false, false> {
  static T handle(std::string option, std::string optionarg) {
    T::unsupported_handleOption_call___please_write_me;
    // The above line causes a compiler error if this version of the template
    // is ever instantiated (meaning that a specialization is missing).  So
    // don't worry about the segfault in the next line, the "return" is only
    // there to keep the compiler from giving additional, distracting errors
    // and warnings.
    return *(T*)0;
  }
};/* struct OptionHandler<T, false, false> */

/** Handle an option of type T in the default way. */
template <class T>
T handleOption(std::string option, std::string optionarg) {
  return OptionHandler<T, std::numeric_limits<T>::is_specialized, std::numeric_limits<T>::is_integer>::handle(option, optionarg);
}

/** Handle an option of type std::string in the default way. */
template <>
std::string handleOption<std::string>(std::string option, std::string optionarg) {
  return optionarg;
}

/**
 * Run handler, and any user-given predicates, for option T.
 * If a user specifies a :handler or :predicates, it overrides this.
 */
template <class T>
typename T::type runHandlerAndPredicates(T, std::string option, std::string optionarg, options::OptionsHandler* handler) {
  // By default, parse the option argument in a way appropriate for its type.
  // E.g., for "unsigned int" options, ensure that the provided argument is
  // a nonnegative integer that fits in the unsigned int type.

  return handleOption<typename T::type>(option, optionarg);
}

template <class T>
void runBoolPredicates(T, std::string option, bool b, options::OptionsHandler* handler) {
  // By default, nothing to do for bool.  Users add things with
  // :predicate in options files to provide custom checking routines
  // that can throw exceptions.
}

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
    //*d_holder = *options.d_holder;
  }
}

void Options::setListener(OptionsListener* ol) { d_olisten = ol; }

// clang-format off

std::vector<std::vector<std::string> > Options::getOptions() const
{
  std::vector< std::vector<std::string> > opts;

  ${options_getoptions}$

  return opts;
}
// clang-format on

}  // namespace cvc5
