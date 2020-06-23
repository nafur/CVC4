#ifndef CVC4__THEORY__NLARITH__CAD__VARIABLE_ORDERING_H
#define CVC4__THEORY__NLARITH__CAD__VARIABLE_ORDERING_H

#include <poly/polyxx.h>

#include "constraints.h"
#include "util/poly_util.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

/** Variable orderings for real variables in the context of CAD. */
enum class VariableOrdering
{
  /** Dummy ordering by variable ID. */
  ByID,
  /** Triangular as of DOI:10.1145/2755996.2756678 */
  Triangular,
  /** Brown as of DOI:10.1145/2755996.2756678 */
  Brown
};

/** Retrieves variable information for all variables with the given polynomials.
 * If with_totals is set, the last element of the vector contains totals as
 * computed by get_variable_information if no variable is specified.
 */
std::vector<poly_utils::VariableInformation> collect_information(
    const Constraints::ConstraintVector& polys, bool with_totals = false);

std::vector<poly::Variable> variable_ordering(
    const Constraints::ConstraintVector& polys, VariableOrdering vo);

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif