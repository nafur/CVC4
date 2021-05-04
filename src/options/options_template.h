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
  struct OptionsHolder;
  ${holder_fwd_decls}$
  class OptionsHandler;
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
  /** Low-level assignment function for options */
  template <class T>
  void assign(T, std::string option, std::string value);
  /** Low-level assignment function for bool-valued options */
  template <class T>
  void assignBool(T, std::string option, bool value);

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

  static std::string formatThreadOptionException(const std::string& option);

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

  /**
   * Set the value of the given option.  Uses `ref()`, which causes a
   * compile-time error if the given option is read-only.
   */
  template <class T>
  void set(T t, const typename T::type& val) {
    ref(t) = val;
  }

  /**
   * Set the default value of the given option. Is equivalent to calling `set()`
   * if `wasSetByUser()` returns false. Uses `ref()`, which causes a compile-time
   * error if the given option is read-only.
   */
  template <class T>
  void setDefault(T t, const typename T::type& val)
  {
    if (!wasSetByUser(t))
    {
      ref(t) = val;
    }
  }

  /**
   * Get a non-const reference to the value of the given option. Causes a
   * compile-time error if the given option is read-only. Writeable options
   * specialize this template with a real implementation.
   */
  template <class T>
  typename T::type& ref(T) {
    // Flag a compile-time error.
    T::you_are_trying_to_get_nonconst_access_to_a_read_only_option;
    // Ensure the compiler does not complain about the return value.
    return *static_cast<typename T::type*>(nullptr);
  }

  /**
   * Set the value of the given option by key.
   *
   * Throws OptionException or ModalException on failures.
   */
  void setOption(const std::string& key, const std::string& optionarg);

  /** Get the value of the given option.  Const access only. */
  template <class T>
  const typename T::type& operator[](T) const;

  /**
   * Gets the value of the given option by key and returns value as a string.
   *
   * Throws OptionException on failures, such as key not being the name of an
   * option.
   */
  std::string getOption(const std::string& key) const;

  /**
   * Returns true iff the value of the given option was set
   * by the user via a command-line option or SmtEngine::setOption().
   * (Options::set() is low-level and doesn't count.)  Returns false
   * otherwise.
   */
  template <class T>
  bool wasSetByUser(T) const;

  /**
   * Get the setting for all options.
   */
  std::vector<std::vector<std::string> > getOptions() const;

  /** Set the generic listener associated with this class to ol */
  void setListener(OptionsListener* ol);

 private:
  /** Pointer to the options listener, if one exists */
  OptionsListener* d_olisten;

}; /* class Options */

}  // namespace cvc5

#endif /* CVC5__OPTIONS__OPTIONS_H */
