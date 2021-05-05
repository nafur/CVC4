/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Interface for custom handlers and predicates options.
 */

#include "cvc5_private.h"

#ifndef CVC5__OPTIONS__OPTIONS_HANDLER_H
#define CVC5__OPTIONS__OPTIONS_HANDLER_H

#include <ostream>
#include <sstream>
#include <string>

#include "options/bv_options.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/printer_modes.h"
#include "options/quantifiers_options.h"

namespace cvc5 {

class Options;

namespace options {

/**
 * Class that responds to command line options being set.
 *
 * Most functions can throw an OptionException on failure.
 */
class OptionsHandler {
public:
  OptionsHandler(Options* options);

  template<typename T>
  void geqZero(const std::string& option, T value) const {
    if (value < 0) {
      std::stringstream ss;
      ss << option << ": " << value << " is not a legal setting, should be " << value << " >= 0.";
      throw OptionException(ss.str());
    }
  }
  template<typename T>
  void betweenZeroAndOne(const std::string& option, T value) const {
    if (value < 0 || value > 1) {
      std::stringstream ss;
      ss << option << ": " << value << " is not a legal setting, should be 0 <= " << option << " <= 1.";
      throw OptionException(ss.str());
    }
  }

  // theory/quantifiers/options_handlers.h
  void checkInstWhenMode(std::string option, InstWhenMode mode);

  // theory/bv/options_handlers.h
  void abcEnabledBuild(std::string option, bool value);
  void abcEnabledBuild(std::string option, std::string value);

  template<class T> void checkSatSolverEnabled(std::string option, T m);

  void checkBvSatSolver(std::string option, SatSolverMode m);
  void checkBitblastMode(std::string option, BitblastMode m);

  void setBitblastAig(std::string option, bool arg);

  // printer/options_handlers.h
  InstFormatMode stringToInstFormatMode(std::string option, std::string optarg);

  // decision/options_handlers.h
  void setDecisionModeStopOnly(std::string option, DecisionMode m);

  /**
   * Throws a ModalException if this option is being set after final
   * initialization.
   */
  void setProduceAssertions(std::string option, bool value);

  void setStats(const std::string& option, bool value);

  unsigned long limitHandler(std::string option, std::string optarg);
  void setResourceWeight(std::string option, std::string optarg);

  /* expr/options_handlers.h */
  void setDefaultExprDepthPredicate(std::string option, int depth);
  void setDefaultDagThreshPredicate(std::string option, int dag);

  /* main/options_handlers.h */
  void copyright(std::string option);
  void showConfiguration(std::string option);
  void showDebugTags(std::string option);
  void showTraceTags(std::string option);
  void threadN(std::string option);

  /* options/base_options_handlers.h */
  void setVerbosity(std::string option, int value);
  void increaseVerbosity(std::string option);
  void decreaseVerbosity(std::string option);
  OutputLanguage stringToOutputLanguage(std::string option, std::string optarg);
  InputLanguage stringToInputLanguage(std::string option, std::string optarg);
  void enableTraceTag(std::string option, std::string optarg);
  void enableDebugTag(std::string option, std::string optarg);

 private:

  /** Pointer to the containing Options object.*/
  Options* d_options;

  /* Help strings */
  static const std::string s_instFormatHelp;

}; /* class OptionHandler */

template<class T>
void OptionsHandler::checkSatSolverEnabled(std::string option, T m)
{
#if !defined(CVC5_USE_CRYPTOMINISAT) && !defined(CVC5_USE_CADICAL) \
    && !defined(CVC5_USE_KISSAT)
  std::stringstream ss;
  ss << "option `" << option
     << "' requires cvc5 to be built with CryptoMiniSat or CaDiCaL or Kissat";
  throw OptionException(ss.str());
#endif
}

}  // namespace options
}  // namespace cvc5

#endif /*  CVC5__OPTIONS__OPTIONS_HANDLER_H */
