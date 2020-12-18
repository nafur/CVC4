/*********************                                                        */
/*! \file cdcac.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements the CDCAC approach.
 **
 ** Implements the CDCAC approach as described in
 ** https://arxiv.org/pdf/2003.05633.pdf.
 **/

#include "theory/arith/nl/cad/cdcac.h"

#ifdef CVC4_POLY_IMP

#include "options/arith_options.h"
#include "theory/arith/nl/cad/projections.h"
#include "theory/arith/nl/cad/variable_ordering.h"

namespace std {
/** Generic streaming operator for std::vector. */
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v)
{
  CVC4::container_to_stream(os, v);
  return os;
}
}  // namespace std

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

namespace {
/** Removed duplicates from a vector. */
template <typename T>
void removeDuplicates(std::vector<T>& v)
{
  std::sort(v.begin(), v.end());
  v.erase(std::unique(v.begin(), v.end()), v.end());
}
}  // namespace

CDCAC::CDCAC() : d_variableOrdering(), d_debugger(d_variableOrdering) {}

CDCAC::CDCAC(const std::vector<poly::Variable>& ordering)
    : d_variableOrdering(ordering), d_debugger(d_variableOrdering)
{
}

std::map<Node, Constraints::Constraint>::iterator CDCAC::preRegisterTerm(TNode n) {
  d_hasNewTerm = true;
  return d_registeredTerms.emplace(n, d_constraints.asConstraint(n)).first;
}

void CDCAC::reset(const std::vector<Node>& assertions)
{
  d_assignment.clear();
  d_constraints.reset();
  for (const Node& a : assertions)
  {
    Trace("cdcac") << "Adding constraint " << a << std::endl;
    auto it = d_registeredTerms.find(a);
    if (it == d_registeredTerms.end()) {
      Trace("cdcac") << "***** Getting surprise term " << a << std::endl;
      it = preRegisterTerm(a);
    }
    Assert(it != d_registeredTerms.end());
    d_constraints.addConstraint(it->second);
  }
  d_tree.check_intervals(assertions);
  d_treeNode = d_tree.getRoot();
}

void CDCAC::computeVariableOrdering()
{
  if (!d_hasNewTerm) return;
  // Actually compute the variable ordering
  auto newVarOrdering = d_varOrder(d_registeredTerms,
                                  VariableOrderingStrategy::BROWN);
  // TODO(Gereon): be more clever about extending the variable order to avoid a full reset
  if (newVarOrdering.size() != d_variableOrdering.size())
  {
    Trace("cdcac") << "Reset as variable ordering changes" << std::endl;
    d_variableOrdering = newVarOrdering;

    // Write variable ordering back to libpoly.
    lp_variable_order_t* vo = poly::Context::get_context().get_variable_order();
    lp_variable_order_clear(vo);
    for (const auto& v : d_variableOrdering)
    {
      lp_variable_order_push(vo, v.get_internal());
    }
    d_tree.clear();
    d_treeNode = d_tree.getRoot();
  }
  Trace("cdcac") << "Variable ordering is now " << d_variableOrdering
                 << std::endl;
}

void CDCAC::retrieveInitialAssignment(NlModel& model, const Node& ran_variable)
{
  if (!options::nlCadUseInitial()) return;
  d_initialAssignment.clear();
  Trace("cdcac") << "Retrieving initial assignment:" << std::endl;
  for (const auto& var : d_variableOrdering)
  {
    Node v = getConstraints().varMapper()(var);
    Node val = model.computeConcreteModelValue(v);
    poly::Value value = node_to_value(val, ran_variable);
    Trace("cdcac") << "\t" << var << " = " << value << std::endl;
    d_initialAssignment.emplace_back(value);
  }
}
Constraints& CDCAC::getConstraints() { return d_constraints; }
const Constraints& CDCAC::getConstraints() const { return d_constraints; }

const poly::Assignment& CDCAC::getModel() const { return d_assignment; }

const std::vector<poly::Variable>& CDCAC::getVariableOrdering() const
{
  return d_variableOrdering;
}

void CDCAC::getUnsatIntervals(
    std::size_t cur_variable) const
{
  Trace("cdcac") << "getUnsatIntervals on level " << cur_variable << std::endl;
  for (const auto& c : d_constraints.getConstraints())
  {
    const poly::Polynomial& p = std::get<0>(c);
    poly::SignCondition sc = std::get<1>(c);
    const Node& n = std::get<2>(c);

    if (main_variable(p) != d_variableOrdering[cur_variable])
    {
      // Constraint is in another variable, ignore it.
      continue;
    }

    Trace("cdcac") << "Infeasible intervals for " << p << " " << sc
                   << " 0 over " << d_assignment << std::endl;
    auto intervals = infeasible_regions(p, d_assignment, sc);
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i << std::endl;
      std::vector<poly::Polynomial> l, u, m, d;
      if (!is_minus_infinity(get_lower(i))) l.emplace_back(p);
      if (!is_plus_infinity(get_upper(i))) u.emplace_back(p);
      m.emplace_back(p);
      CACInterval interval{i, l, u, m, d, {n}};
      d_treeNode->addDirectConflict(interval);
    }
  }
}

bool CDCAC::sampleOutsideWithInitial(poly::Value& sample,
                                     std::size_t cur_variable)
{
  CDCACTree::TreeNode* next = d_tree.sampleOutside(d_treeNode);
  Trace("cdcac") << "Descending from " << static_cast<const void*>(d_treeNode) << " to " << static_cast<const void*>(next) << std::endl;
  if (next != nullptr) {
    d_treeNode = next;
    Assert(d_treeNode->sample);
    sample = d_treeNode->sample.value();
    return true;
  }
  return false;
  /*
  if (options::nlCadUseInitial() && cur_variable < d_initialAssignment.size())
  {
    const poly::Value& suggested = d_initialAssignment[cur_variable];
    for (const auto& i : infeasible)
    {
      if (poly::contains(i.d_interval, suggested))
      {
        d_initialAssignment.clear();
        return sampleOutside(infeasible, sample);
      }
    }
    Trace("cdcac") << "Using suggested initial value" << std::endl;
    sample = suggested;
    return true;
  }
  return sampleOutside(infeasible, sample);
  */
}

std::vector<poly::Polynomial> CDCAC::requiredCoefficients(
    const poly::Polynomial& p) const
{
  std::vector<poly::Polynomial> res;
  for (long deg = degree(p); deg >= 0; --deg)
  {
    auto coeff = coefficient(p, deg);
    if (lp_polynomial_is_constant(coeff.get_internal())) break;
    res.emplace_back(coeff);
    if (evaluate_constraint(coeff, d_assignment, poly::SignCondition::NE))
    {
      break;
    }
  }
  return res;
}

std::vector<poly::Polynomial> CDCAC::constructCharacterization(
    std::vector<CACInterval>& intervals)
{
  Assert(!intervals.empty()) << "A covering can not be empty";
  Trace("cdcac") << "Constructing characterization now" << std::endl;
  std::vector<poly::Polynomial> res;

  for (std::size_t i = 0, n = intervals.size(); i < n - 1; ++i)
  {
    cad::makeFinestSquareFreeBasis(intervals[i], intervals[i + 1]);
  }

  for (const auto& i : intervals)
  {
    Trace("cdcac") << "Considering " << i.d_interval << std::endl;
    Trace("cdcac") << "-> " << i.d_lowerPolys << " / " << i.d_upperPolys
                   << " and " << i.d_mainPolys << " / " << i.d_downPolys
                   << std::endl;
    Trace("cdcac") << "-> " << i.d_origins << std::endl;
    for (const auto& p : i.d_downPolys)
    {
      // Add all polynomial from lower levels.
      addPolynomial(res, p);
    }
    for (const auto& p : i.d_mainPolys)
    {
      Trace("cdcac") << "Discriminant of " << p << " -> " << discriminant(p)
                     << std::endl;
      // Add all discriminants
      addPolynomial(res, discriminant(p));

      for (const auto& q : requiredCoefficients(p))
      {
        // Add all required coefficients
        Trace("cdcac") << "Coeff of " << p << " -> " << q << std::endl;
        addPolynomial(res, q);
      }
      for (const auto& q : i.d_lowerPolys)
      {
        if (p == q) continue;
        // Check whether p(s \times a) = 0 for some a <= l
        if (!hasRootBelow(q, get_lower(i.d_interval))) continue;
        Trace("cdcac") << "Resultant of " << p << " and " << q << " -> "
                       << resultant(p, q) << std::endl;
        addPolynomial(res, resultant(p, q));
      }
      for (const auto& q : i.d_upperPolys)
      {
        if (p == q) continue;
        // Check whether p(s \times a) = 0 for some a >= u
        if (!hasRootAbove(q, get_upper(i.d_interval))) continue;
        Trace("cdcac") << "Resultant of " << p << " and " << q << " -> "
                       << resultant(p, q) << std::endl;
        addPolynomial(res, resultant(p, q));
      }
    }
  }

  for (std::size_t i = 0, n = intervals.size(); i < n - 1; ++i)
  {
    // Add resultants of consecutive intervals.
    for (const auto& p : intervals[i].d_upperPolys)
    {
      for (const auto& q : intervals[i + 1].d_lowerPolys)
      {
        Trace("cdcac") << "Resultant of " << p << " and " << q << " -> "
                       << resultant(p, q) << std::endl;
        addPolynomial(res, resultant(p, q));
      }
    }
  }

  removeDuplicates(res);
  makeFinestSquareFreeBasis(res);

  return res;
}

CACInterval CDCAC::intervalFromCharacterization(
    const std::vector<poly::Polynomial>& characterization,
    std::size_t cur_variable,
    const poly::Value& sample)
{
  std::vector<poly::Polynomial> l;
  std::vector<poly::Polynomial> u;
  std::vector<poly::Polynomial> m;
  std::vector<poly::Polynomial> d;

  for (const auto& p : characterization)
  {
    // Add polynomials to either main or down
    if (main_variable(p) == d_variableOrdering[cur_variable])
    {
      m.emplace_back(p);
    }
    else
    {
      d.emplace_back(p);
    }
  }

  // Collect -oo, all roots, oo
  std::vector<poly::Value> roots;
  roots.emplace_back(poly::Value::minus_infty());
  for (const auto& p : m)
  {
    auto tmp = isolate_real_roots(p, d_assignment);
    roots.insert(roots.end(), tmp.begin(), tmp.end());
  }
  roots.emplace_back(poly::Value::plus_infty());
  std::sort(roots.begin(), roots.end());

  // Now find the interval bounds
  poly::Value lower;
  poly::Value upper;
  for (std::size_t i = 0, n = roots.size(); i < n; ++i)
  {
    if (sample < roots[i])
    {
      lower = roots[i - 1];
      upper = roots[i];
      break;
    }
    if (roots[i] == sample)
    {
      lower = sample;
      upper = sample;
      break;
    }
  }
  Assert(!is_none(lower) && !is_none(upper));

  if (!is_minus_infinity(lower))
  {
    // Identify polynomials that have a root at the lower bound
    d_assignment.set(d_variableOrdering[cur_variable], lower);
    for (const auto& p : m)
    {
      if (evaluate_constraint(p, d_assignment, poly::SignCondition::EQ))
      {
        l.emplace_back(p);
      }
    }
    d_assignment.unset(d_variableOrdering[cur_variable]);
  }
  if (!is_plus_infinity(upper))
  {
    // Identify polynomials that have a root at the upper bound
    d_assignment.set(d_variableOrdering[cur_variable], upper);
    for (const auto& p : m)
    {
      if (evaluate_constraint(p, d_assignment, poly::SignCondition::EQ))
      {
        u.emplace_back(p);
      }
    }
    d_assignment.unset(d_variableOrdering[cur_variable]);
  }

  if (lower == upper)
  {
    // construct a point interval
    return CACInterval{
        poly::Interval(lower, false, upper, false), l, u, m, d, {}};
  }
  else
  {
    // construct an open interval
    Assert(lower < upper);
    return CACInterval{
        poly::Interval(lower, true, upper, true), l, u, m, d, {}};
  }
}

bool CDCAC::getUnsatCover(std::size_t curVariable,
                                              bool returnFirstInterval)
{
  if (curVariable == 0)
  {
    Trace("cdcac") << "******************** CDCAC Check" << std::endl;
    for (const auto& c : d_constraints.getConstraints())
    {
      Trace("cdcac") << "-> " << std::get<0>(c) << " " << std::get<1>(c)
                     << " 0 from " << std::get<2>(c) << std::endl;
    }
  }
  Trace("cdcac") << "Looking for unsat cover for "
                 << d_variableOrdering[curVariable] << std::endl;
  getUnsatIntervals(curVariable);

  if (Trace.isOn("cdcac"))
  {
    Trace("cdcac") << "Unsat intervals for " << d_variableOrdering[curVariable]
                   << ":" << std::endl;
    for (const auto& child : d_treeNode->children)
    {
      Trace("cdcac") << "-> " << *child << std::endl;
    }
  }
  poly::Value sample;

  while (sampleOutsideWithInitial(sample, curVariable))
  {
    if (!checkIntegrality(curVariable, sample))
    {
      // the variable is integral, but the sample is not.
      Trace("cdcac") << "Used " << sample << " for integer variable "
                     << d_variableOrdering[curVariable] << std::endl;
      auto newInterval = buildIntegralityInterval(curVariable, sample);
      Trace("cdcac") << "Adding integrality interval " << newInterval.d_interval
                     << std::endl;
      //intervals.emplace_back(newInterval);
      //cleanIntervals(intervals);
      if (use_incremental) {
        AlwaysAssert(false) << "Need to handle integrality interval " << newInterval.d_interval << std::endl;
      }
      continue;
    }
    d_assignment.set(d_variableOrdering[curVariable], sample);
    Trace("cdcac") << "Sample: " << d_assignment << std::endl;
    Trace("cdcac") << *d_treeNode << std::endl;
    Trace("cdcac") << d_tree << std::endl;
    Assert(d_treeNode->sample && d_treeNode->sample.value() == sample);
    if (curVariable == d_variableOrdering.size() - 1)
    {
      // We have a full assignment. SAT!
      Trace("cdcac") << "Found full assignment: " << d_assignment << std::endl;
      return true;
    }
    // Recurse to next variable
    bool isSat = getUnsatCover(curVariable + 1);
    if (isSat)
    {
      // Found SAT!
      Trace("cdcac") << "SAT!" << std::endl;
      return true;
    }
    Trace("cdcac") << "Refuting Sample: " << d_assignment << std::endl;
    std::vector<CACInterval> intervals = d_treeNode->collectChildIntervals();
    if (Trace.isOn("cdcac"))
    {
      Trace("cdcac") << "Unsat intervals for " << d_variableOrdering[curVariable]
                    << ":" << std::endl;
      for (const auto& child : d_treeNode->children)
      {
        Trace("cdcac") << "-> " << *child << std::endl;
      }
    }
    auto characterization = constructCharacterization(intervals);
    Trace("cdcac") << "Characterization: " << characterization << std::endl;

    d_assignment.unset(d_variableOrdering[curVariable]);

    auto newInterval =
        intervalFromCharacterization(characterization, curVariable, sample);
    newInterval.d_origins = collectConstraints(intervals);
    d_treeNode->intervals.emplace_back(newInterval);
    d_treeNode = d_treeNode->parent;
    Assert(d_treeNode != nullptr);
    Trace("cdcac") << *d_treeNode << std::endl;
    Trace("cdcac") << d_tree << std::endl;

    if (returnFirstInterval)
    {
      return false;
    }

    Trace("cdcac") << "Added " << newInterval.d_interval << std::endl;
    Trace("cdcac") << "\tlower:   " << newInterval.d_lowerPolys
                   << std::endl;
    Trace("cdcac") << "\tupper:   " << newInterval.d_upperPolys
                   << std::endl;
    Trace("cdcac") << "\tmain:    " << newInterval.d_mainPolys
                   << std::endl;
    Trace("cdcac") << "\tdown:    " << newInterval.d_downPolys
                   << std::endl;
    Trace("cdcac") << "\torigins: " << newInterval.d_origins << std::endl;

  }

  Trace("cdcac") << *d_treeNode << std::endl;
  Trace("cdcac") << d_tree << std::endl;

  return false;
}

bool CDCAC::checkIntegrality(std::size_t cur_variable, const poly::Value& value)
{
  Node var = d_constraints.varMapper()(d_variableOrdering[cur_variable]);
  if (var.getType() != NodeManager::currentNM()->integerType())
  {
    // variable is not integral
    return true;
  }
  return poly::represents_integer(value);
}

CACInterval CDCAC::buildIntegralityInterval(std::size_t cur_variable,
                                            const poly::Value& value)
{
  poly::Variable var = d_variableOrdering[cur_variable];
  poly::Integer below = poly::floor(value);
  poly::Integer above = poly::ceil(value);
  // construct var \in (below, above)
  return CACInterval{poly::Interval(below, above),
                     {var - below},
                     {var - above},
                     {var - below, var - above},
                     {},
                     {}};
}

bool CDCAC::hasRootAbove(const poly::Polynomial& p,
                         const poly::Value& val) const
{
  auto roots = poly::isolate_real_roots(p, d_assignment);
  return std::any_of(roots.begin(), roots.end(), [&val](const poly::Value& r) {
    return r >= val;
  });
}

bool CDCAC::hasRootBelow(const poly::Polynomial& p,
                         const poly::Value& val) const
{
  auto roots = poly::isolate_real_roots(p, d_assignment);
  return std::any_of(roots.begin(), roots.end(), [&val](const poly::Value& r) {
    return r <= val;
  });
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
