#ifndef CVC4__THEORY__NLARITH__CAD__CDCAC_H
#define CVC4__THEORY__NLARITH__CAD__CDCAC_H

#include <poly/polyxx.h>

#include <vector>

#include "../nl_model.h"
#include "cdcac_utils.h"
#include "constraints.h"
#include "variable_ordering.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

using namespace poly;

class CDCAC
{
  /** The current assignment. Also contains a model if the method terminates
   * with SAT. */
  Assignment mAssignment;
  /** The set of constraints to be checked. */
  Constraints mConstraints;

  /** The variable ordering used for this method. */
  std::vector<Variable> mVariableOrdering;

  /** The linear assignment used as an initial guess. */
  std::vector<poly::Value> mInitialAssignment;

  VariableOrdering mVarOrder;

  CDCACDebugger debugger;

 public:
  /** Initialize without a variable ordering. */
  CDCAC();
  /** Initialize this method with the given variable ordering.
   */
  CDCAC(const std::vector<Variable>& ordering);

  /** Reset this instance. */
  void reset();

  /** Collect variables from the constraints and compute a variable ordering. */
  void compute_variable_ordering();

  void retrieve_initial_assignment(NlModel& model, const Node& ran_variable);

  /** Returns the constraints as a non-const reference. Can be used to add new
   * constraints. */
  Constraints& get_constraints();
  /** Returns the constraints as a const reference. */
  const Constraints& get_constraints() const;

  /** Returns the current assignment. This is a satisfying model if
   * get_unsat_cover() returned an empty vector. */
  const Assignment& get_model() const;

  /** Returns the current variable ordering. */
  const std::vector<Variable>& get_variable_ordering() const;

  /** Collect all unsatisfiable intervals.
   * Combines unsatisfiable regions from mConstraints evaluated over
   * mAssignment. Implements Algorithm 2.
   */
  std::vector<CACInterval> get_unsat_intervals(std::size_t cur_variable) const;

  /** Sample outside of the set of intervals.
   * Uses a given initial value from mInitialAssignment if possible.
   */
  bool sample_outside_with_initial(const std::vector<CACInterval>& infeasible,
                                   poly::Value& sample,
                                   std::size_t cur_variable);

  /** Collects the coefficients required for projection from the given
   * polynomial. Implements Algorithm 6.
   */
  std::vector<Polynomial> required_coefficients(const Polynomial& p) const;

  /** Constructs a characterization of the given covering.
   * A characterization contains polynomials whose roots bound the region around
   * the current assignment. Implements Algorithm 4.
   */
  std::vector<Polynomial> construct_characterization(
      std::vector<CACInterval>& intervals);

  /** Constructs an infeasible interval from a characterization.
   * Implements Algorithm 5.
   */
  CACInterval interval_from_characterization(
      const std::vector<Polynomial>& characterization,
      std::size_t cur_variable,
      const Value& sample);

  /** Main method that checks for the satisfiability of the constraints.
   * Recursively explores possible assignments and excludes regions based on the
   * coverings. Returns either a covering for the lowest dimension or an empty
   * vector. If the covering is empty, the result is SAT and an assignment can
   * be obtained from mAssignment. If the covering is not empty, the result is
   * UNSAT and an infeasible subset can be extracted from the returned covering.
   * Implements Algorithm 2.
   */
  std::vector<CACInterval> get_unsat_cover(std::size_t cur_variable = 0,
                                           bool return_first_interval = false);
};

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif