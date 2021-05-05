/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Paul Meng
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_API_H
#define CVC5__OPTIONS__OPTIONS_API_H

#include <iosfwd>
#include <string>
#include <vector>

#include "cvc5_export.h"

namespace cvc5 {
    class Options;
}

namespace cvc5::options {
    class OptionsHandler;

  /**
   * Get a description of the command-line flags accepted by
   * parseOptions.  The returned string will be escaped so that it is
   * suitable as an argument to printf. */
  const std::string& getDescription() CVC5_EXPORT;

  /**
   * Print overall command-line option usage message, prefixed by
   * "msg"---which could be an error message causing the usage
   * output in the first place, e.g. "no such option --foo"
   */
  void printUsage(const std::string& msg, std::ostream& os) CVC5_EXPORT;

  /**
   * Print command-line option usage message for only the most-commonly
   * used options.  The message is prefixed by "msg"---which could be
   * an error message causing the usage output in the first place, e.g.
   * "no such option --foo"
   */
  void printShortUsage(const std::string& msg, std::ostream& os) CVC5_EXPORT;

  /** Print help for the --lang command line option */
  void printLanguageHelp(std::ostream& os) CVC5_EXPORT;

  /**
   * Initialize the Options object options based on the given
   * command-line arguments given in argc and argv.  The return value
   * is what's left of the command line (that is, the non-option
   * arguments).
   *
   * This function uses getopt_long() and is not thread safe.
   *
   * Throws OptionException on failures.
   *
   * Preconditions: options and argv must be non-null.
   */
  std::vector<std::string> parseOptions(Options* options,
                                               int argc,
                                               char* argv[]) CVC5_EXPORT;

    std::string get(const Options& options, const std::string& key);
    void set(Options& options, const std::string& key, const std::string& optionarg);

  /**
   * Get the setting for all options.
   */
  std::vector<std::vector<std::string> > getAll(const Options& opts);

}  // namespace cvc5::options

#endif /* CVC5__OPTIONS__OPTIONS_H */
