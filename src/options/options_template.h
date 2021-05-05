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

#ifndef CVC5__OPTIONS__OPTIONS_H
#define CVC5__OPTIONS__OPTIONS_H

#include <iosfwd>
#include <memory>
#include <string>
#include <vector>

#include "base/listener.h"
#include "cvc5_export.h"

namespace cvc5 {
class Options;

namespace api {
class Solver;
}
namespace options {
  class OptionsHandler;
${holder_fwd_decls}$
}  // namespace options

class OptionsListener;

class CVC5_EXPORT Options
{
  public:
${holder_mem_decls}$

  /** The handler for the options of the theory. */
  options::OptionsHandler* d_handler;
  private:
  friend api::Solver;

public:
  /** The current Options in effect */
  static thread_local Options* s_current;
private:

  friend class options::OptionsHandler;

  /**
   * Options cannot be copied as they are given an explicit list of
   * Listeners to respond to.
   */
  Options(const Options& options) = delete;

  /**
   * Options cannot be assigned as they are given an explicit list of
   * Listeners to respond to.
   */
  Options& operator=(const Options& options) = delete;

public:
 class OptionsScope
 {
  private:
    Options* d_oldOptions;
  public:
    OptionsScope(Options* newOptions) :
        d_oldOptions(Options::s_current)
    {
      Options::s_current = newOptions;
    }
    ~OptionsScope(){
      Options::s_current = d_oldOptions;
    }
 };

  /** Return true if current Options are null */
  static inline bool isCurrentNull() {
    return s_current == NULL;
  }

  /** Get the current Options in effect */
  static inline Options& current() {
    return *s_current;
  }

  Options(OptionsListener* ol = nullptr);
  ~Options();

  /**
   * Copies the value of the options stored in OptionsHolder into the current
   * Options object.
   * This does not copy the listeners in the Options object.
   */
  void copyValues(const Options& options);

  public:

  /**
   * Get the setting for all options.
   */
  std::vector<std::vector<std::string> > getOptions() const;

  /** Set the generic listener associated with this class to ol */
  void setListener(OptionsListener* ol);

 public:
  /** Pointer to the options listener, if one exists */
  OptionsListener* d_olisten;

}; /* class Options */

}  // namespace cvc5

#endif /* CVC5__OPTIONS__OPTIONS_H */
