/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Public facing functions for options that need to be accessed from the outside.
 * 
 * These are all 1 line wrappers for `Options::operator[]`, `Options::set()` and
 * `Options::wasSetByUser()` so that external code (including parser/ and main/)
 * does not need to include the option modules (*_options.h).
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_PUBLIC_H
#define CVC5__OPTIONS__OPTIONS_PUBLIC_H

#include "options/options.h"

namespace cvc5::options
{

InputLanguage getInputLanguage(const Options& opts);
InstFormatMode getInstFormatMode(const Options& opts);
OutputLanguage getOutputLanguage(const Options& opts);
bool getUfHo(const Options& opts);
bool getDumpInstantiations(const Options& opts);
bool getDumpModels(const Options& opts);
bool getDumpProofs(const Options& opts);
bool getDumpUnsatCores(const Options& opts);
bool getEarlyExit(const Options& opts);
bool getFilesystemAccess(const Options& opts);
bool getForceNoLimitCpuWhileDump(const Options& opts);
bool getHelp(const Options& opts);
bool getIncrementalSolving(const Options& opts);
bool getInteractive(const Options& opts);
bool getInteractivePrompt(const Options& opts);
bool getLanguageHelp(const Options& opts);
bool getMemoryMap(const Options& opts);
bool getParseOnly(const Options& opts);
bool getProduceModels(const Options& opts);
bool getSegvSpin(const Options& opts);
bool getSemanticChecks(const Options& opts);
bool getStatistics(const Options& opts);
bool getStatsEveryQuery(const Options& opts);
bool getStrictParsing(const Options& opts);
int getTearDownIncremental(const Options& opts);
unsigned long getCumulativeTimeLimit(const Options& opts);
bool getVersion(const Options& opts);
const std::string& getForceLogicString(const Options& opts);
int getVerbosity(const Options& opts);

std::istream* getIn(const Options& opts);
std::ostream* getErr(const Options& opts);
std::ostream* getOut(const Options& opts);
const std::string& getBinaryName(const Options& opts);


bool wasSetByUserEarlyExit(const Options& opts);
bool wasSetByUserForceLogicString(const Options& opts);
bool wasSetByUserIncrementalSolving(const Options& opts);
bool wasSetByUserInteractive(const Options& opts);

}

#endif
