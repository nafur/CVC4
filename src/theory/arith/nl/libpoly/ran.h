
#ifndef CVC4__THEORY__NLARITH__LIBPOLY__RAN_H
#define CVC4__THEORY__NLARITH__LIBPOLY__RAN_H

#include <poly/algebraic_number.h>

#include <iostream>

#include "dyadic_interval.h"
#include "integer.h"
#include "upolynomial.h"
#include "utils.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace libpoly {

/**
 * Implements a wrapper for lp_algebraic_number_t from libpoly.
 */
class RAN
{
  /** The actual algebraic number. */
  lp_algebraic_number_t mValue;

 public:
  RAN() {
    lp_algebraic_number_construct_zero(&mValue);
  }
  /** Construct from a defining polynomial and an isolating interval. */
  RAN(UPolynomial&& poly, const DyadicInterval& i);
  /** Construct from a defining polynomial and an isolating interval. */
  RAN(const UPolynomial& poly, const DyadicInterval& i);
  /** Construct from a lp_algebraic_number_t, copying its contents. */
  RAN(const lp_algebraic_number_t& ran);
  /** Copy from the given RAN. */
  RAN(const RAN& ran);
  /** Move from the given RAN. */
  RAN(RAN&& ran);
  /** Custom destructor. */
  ~RAN();
  /** Assign from the given RAN. */
  RAN& operator=(RAN r);

  /** Get a non-const pointer to the internal lp_algebraic_number_t. Handle with
   * care! */
  lp_algebraic_number_t* get();
  /** Get a const pointer to the internal lp_algebraic_number_t. */
  const lp_algebraic_number_t* get() const;
};
/** Stream the given RAN to an output stream. */
std::ostream& operator<<(std::ostream& os, const RAN& v);

/** Compare two RANs for equality. */
bool operator==(const RAN& lhs, const RAN& rhs);
/** Compare a RAN and an Integer for equality. */
bool operator==(const RAN& lhs, const Integer& rhs);
/** Compare an Integer and a RAN for equality. */
bool operator==(const Integer& lhs, const RAN& rhs);

}  // namespace libpoly
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
