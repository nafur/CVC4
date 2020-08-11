/*********************                                                        */
/*! \file candidate.cpp
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

#include "theory/arith/nl/icp/candidate.h"

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "theory/arith/nl/poly_conversion.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

PropagationResult Candidate::propagate(poly::IntervalAssignment& ia) const {
        auto res = poly::evaluate(rhs, ia) * poly::Interval(poly::Value(rhsmult));
        Trace("nl-icp") << "Prop: " << *this << " -> " << res << std::endl;
        switch (rel) {
            case poly::SignCondition::LT:
                res.set_lower(poly::Value::minus_infty(), true);
                res.set_upper(get_upper(res), true);
                break;
            case poly::SignCondition::LE: res.set_lower(poly::Value::minus_infty(), true); break;
            case poly::SignCondition::EQ: break;
            case poly::SignCondition::NE: Assert(false); break;
            case poly::SignCondition::GT:
                res.set_lower(get_lower(res), true);
                res.set_upper(poly::Value::plus_infty(), true);
                break;
            case poly::SignCondition::GE: res.set_upper(poly::Value::plus_infty(), true); break;
        }
        auto cur = ia.get(lhs);
        Trace("nl-icp") << "-> " << res << " used to update " << cur << std::endl;

        PropagationResult result = intersect_interval_with(cur, res);
        switch (result) {
            case PropagationResult::CONTRACTED:
            case PropagationResult::CONTRACTED_WITHOUT_CURRENT: {
                Trace("nl-icp") << *this << " contracted " << lhs << " -> " << cur << std::endl;
                auto old = ia.get(lhs);
                bool strong = false;
                strong = strong || (is_minus_infinity(get_lower(old)) && !is_minus_infinity(get_lower(cur)));
                strong = strong || (is_plus_infinity(get_upper(old)) && !is_plus_infinity(get_upper(cur)));
                ia.set(lhs, cur);
                if (strong) {
                    if (result == PropagationResult::CONTRACTED) {
                        result = PropagationResult::CONTRACTED_STRONGLY;
                    } else if (result == PropagationResult::CONTRACTED_WITHOUT_CURRENT) {
                        result = PropagationResult::CONTRACTED_STRONGLY_WITHOUT_CURRENT;
                    }
                }
                break;
            }
            case PropagationResult::CONTRACTED_STRONGLY:
            case PropagationResult::CONTRACTED_STRONGLY_WITHOUT_CURRENT:
                Assert(false) << "This method should not return strong flags.";
                break;
            default:
                break;
        }
        return result;
    }

std::ostream& operator<<(std::ostream& os, const Candidate& c) {
    os << c.lhs << " " << c.rel << " ";
    if (c.rhsmult != poly::Rational(1)) os << c.rhsmult << " * ";
    return os << c.rhs;
}

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
