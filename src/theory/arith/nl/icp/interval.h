/*********************                                                        */
/*! \file interval.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **/

#ifndef CVC4__THEORY__ARITH__ICP__INTERVAL_H
#define CVC4__THEORY__ARITH__ICP__INTERVAL_H

#include <poly/polyxx.h>

#include "expr/node.h"
#include "util/poly_util.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

struct Interval
{
  poly::Value lower = poly::Value::minus_infty();
  bool lower_strict = true;
  Node lower_origin;
  poly::Value upper = poly::Value::plus_infty();
  bool upper_strict = true;
  Node upper_origin;
};

inline std::ostream& operator<<(std::ostream& os, const Interval& i)
{
  return os << (i.lower_strict ? '(' : '[') << i.lower << " .. " << i.upper
            << (i.upper_strict ? ')' : ']');
}

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
