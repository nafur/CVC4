/*********************                                                        */
/*! \file cdcac_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements utilities for cdcac.
 **
 ** Implements utilities for cdcac.
 **/

#ifndef CVC4__THEORY__ARITH__NL__CAD__CDCAC_UTILS_H
#define CVC4__THEORY__ARITH__NL__CAD__CDCAC_UTILS_H

#include <poly/polyxx.h>

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

/**
 * An interval as specified in section 4.1 of
 * https://arxiv.org/pdf/2003.05633.pdf.
 *
 * It consists of
 * - the actual interval, either an open or a point interal,
 * - the characterizing polynomials of the lower and upper bound,
 * - the characterizing polynomials in the main variable,
 * - the characterizing polynomials in lower variables and
 * - the constraints used to derive this interval.
 */
struct CACInterval
{
  /** The actual interval. */
  poly::Interval mInterval;
  /** The polynomials characterizing the lower bound. */
  std::vector<poly::Polynomial> mLowerPolys;
  /** The polynomials characterizing the upper bound. */
  std::vector<poly::Polynomial> mUpperPolys;
  /** The characterizing polynomials in the main variable. */
  std::vector<poly::Polynomial> mMainPolys;
  /** The characterizing polynomials in lower variables. */
  std::vector<poly::Polynomial> mDownPolys;
  /** The constraints used to derive this interval. */
  std::vector<Node> mOrigins;
};
/** Check whether to intervals are the same. */
inline bool operator==(const CACInterval& lhs, const CACInterval& rhs)
{
  return lhs.mInterval == rhs.mInterval;
}
/** Compare two intervals. */
inline bool operator<(const CACInterval& lhs, const CACInterval& rhs)
{
  return lhs.mInterval < rhs.mInterval;
}

/** Check whether lhs covers rhs. */
bool interval_covers(const poly::Interval& lhs, const poly::Interval& rhs);
/**
 * Check whether two intervals connect, assuming lhs < rhs.
 * They connect, if their union has no gap.
 */
bool interval_connect(const poly::Interval& lhs, const poly::Interval& rhs);

/**
 * Sort intervals according to section 4.4.1.
 * Also removes fully redundant intervals as in 4.5. 1.
 */
void clean_intervals(std::vector<CACInterval>& intervals);

/**
 * Collect all origins from the list of intervals to construct the origins for a
 * whole covering.
 */
std::vector<Node> collect_constraints(
    const std::vector<CACInterval>& intervals);

/**
 * Sample a point outside of the infeasible intervals.
 * Stores the sample in sample, returns whether such a sample exists.
 * If false is returned, the infeasible intervals cover the real line.
 * Implements sample_outside() from section 4.3
 */
bool sample_outside(const std::vector<CACInterval>& infeasible,
                    poly::Value& sample);

class CDCACDebugger
{
  std::size_t mCheckCounter = 0;
  const std::vector<poly::Variable>& mVariables;

 public:
  CDCACDebugger(const std::vector<poly::Variable>& vars) : mVariables(vars) {}
  void check_interval(const poly::Assignment& a,
                      const poly::Variable& variable,
                      const CACInterval& i);
};

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
