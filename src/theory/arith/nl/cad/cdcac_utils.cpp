#include "cdcac_utils.h"

#include <fstream>

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

using namespace poly;

/** Induces an ordering on poly intervals that is suitable for redundancy
 * removal as implemented in clean_intervals.
 */
inline bool compare_for_cleanup(const Interval& lhs, const Interval& rhs)
{
  const lp_value_t* ll = &(lhs.get_internal()->a);
  const lp_value_t* lu =
      lhs.get_internal()->is_point ? ll : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  const lp_value_t* ru =
      rhs.get_internal()->is_point ? rl : &(rhs.get_internal()->b);

  int lc = lp_value_cmp(ll, rl);
  // Lower bound is smaller
  if (lc < 0) return true;
  // Lower bound is larger
  if (lc > 0) return false;
  // Lower bound type is smaller
  if (!lhs.get_internal()->a_open && rhs.get_internal()->a_open) return true;
  // Lower bound type is larger
  if (lhs.get_internal()->a_open && !rhs.get_internal()->a_open) return false;

  // Attention: Here it differs from the regular interval ordering!
  int uc = lp_value_cmp(lu, ru);
  // Upper bound is smaller
  if (uc < 0) return false;
  // Upper bound is larger
  if (uc > 0) return true;
  // Upper bound type is smaller
  if (lhs.get_internal()->b_open && !rhs.get_internal()->b_open) return false;
  // Upper bound type is larger
  if (!lhs.get_internal()->b_open && rhs.get_internal()->b_open) return true;

  // Identical
  return false;
}

bool interval_covers(const Interval& lhs, const Interval& rhs)
{
  const lp_value_t* ll = &(lhs.get_internal()->a);
  const lp_value_t* lu =
      lhs.get_internal()->is_point ? ll : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  const lp_value_t* ru =
      rhs.get_internal()->is_point ? rl : &(rhs.get_internal()->b);

  int lc = lp_value_cmp(ll, rl);
  int uc = lp_value_cmp(lu, ru);

  // Lower bound is smaller and upper bound is larger
  if (lc < 0 && uc > 0) return true;
  // Lower bound is larger or upper bound is smaller
  if (lc > 0 || uc < 0) return false;

  // Now both bounds are identical.
  Assert(lc <= 0 && uc >= 0);
  Assert(lc == 0 || uc == 0);

  // Lower bound is the same and the bound type is stricter
  if (lc == 0 && lhs.get_internal()->a_open && !rhs.get_internal()->a_open)
    return false;
  // Upper bound is the same and the bound type is stricter
  if (uc == 0 && lhs.get_internal()->b_open && !rhs.get_internal()->b_open)
    return false;

  // Both bounds are weaker
  return true;
}

bool interval_connect(const Interval& lhs, const Interval& rhs)
{
  Assert(lhs < rhs) << "Can only check for a connection if lhs < rhs.";
  const lp_value_t* lu = lhs.get_internal()->is_point
                             ? &(lhs.get_internal()->a)
                             : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  int c = lp_value_cmp(lu, rl);
  if (c < 0)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs << " are separated." << std::endl;
    return false;
  }
  if (c > 0)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs << " overlap." << std::endl;
    return true;
  }
  Assert(c == 0);
  if (lhs.get_internal()->is_point || rhs.get_internal()->is_point
      || !lhs.get_internal()->b_open || !rhs.get_internal()->a_open)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs
        << " touch and the intermediate point is covered." << std::endl;
    return true;
  }
  return false;
}

void clean_intervals(std::vector<CACInterval>& intervals)
{
  // Simplifies removal of redundancies later on.
  if (intervals.size() < 2) return;

  // Sort intervals.
  std::sort(intervals.begin(),
            intervals.end(),
            [](const CACInterval& lhs, const CACInterval& rhs) {
              return compare_for_cleanup(lhs.mInterval, rhs.mInterval);
            });

  // Remove intervals that are covered by others.
  // Implementation roughly follows
  // https://en.cppreference.com/w/cpp/algorithm/remove Find first interval that
  // covers the next one.
  std::size_t first = 0;
  for (; first < intervals.size() - 1; ++first)
  {
    if (interval_covers(intervals[first].mInterval,
                        intervals[first + 1].mInterval))
    {
      break;
    }
  }
  // If such an interval exists, remove accordingly.
  if (first < intervals.size() - 1)
  {
    for (std::size_t i = first + 2; i < intervals.size(); ++i)
    {
      if (!interval_covers(intervals[first].mInterval, intervals[i].mInterval))
      {
        // Interval is not covered. Move it to the front and bump front.
        ++first;
        intervals[first] = std::move(intervals[i]);
      }
      // Else: Interval is covered as well.
    }
    // Erase trailing values
    while (intervals.size() > first + 1)
    {
      intervals.pop_back();
    }
  }
}

std::vector<Node> collect_constraints(const std::vector<CACInterval>& intervals)
{
  std::vector<Node> res;
  for (const auto& i : intervals)
  {
    res.insert(res.end(), i.mOrigins.begin(), i.mOrigins.end());
  }
  std::sort(res.begin(), res.end());
  auto it = std::unique(res.begin(), res.end());
  res.erase(it, res.end());
  return res;
}

bool sample_outside(const std::vector<CACInterval>& infeasible, Value& sample)
{
  if (infeasible.empty())
  {
    sample = poly::Integer();
    return true;
  }
  if (!is_minus_infinity(get_lower(infeasible.front().mInterval)))
  {
    Trace("cdcac") << "Sample before " << infeasible.front().mInterval
                   << std::endl;
    const auto* i = infeasible.front().mInterval.get_internal();
    sample = value_between(
        Value::minus_infty().get_internal(), true, &i->a, !i->a_open);
    return true;
  }
  for (std::size_t i = 0; i < infeasible.size() - 1; ++i)
  {
    if (!interval_connect(infeasible[i].mInterval, infeasible[i + 1].mInterval))
    {
      const auto* l = infeasible[i].mInterval.get_internal();
      const auto* r = infeasible[i + 1].mInterval.get_internal();

      Trace("cdcac") << "Sample between " << infeasible[i].mInterval << " and "
                     << infeasible[i + 1].mInterval << std::endl;

      if (l->is_point)
      {
        sample = value_between(&l->a, true, &r->a, !r->a_open);
      }
      else
      {
        sample = value_between(&l->b, !l->b_open, &r->a, !r->a_open);
      }
      return true;
    }
    else
    {
      Trace("cdcac") << infeasible[i].mInterval << " and "
                     << infeasible[i + 1].mInterval << " connect" << std::endl;
    }
  }
  if (!is_plus_infinity(get_upper(infeasible.back().mInterval)))
  {
    Trace("cdcac") << "Sample above " << infeasible.back().mInterval
                   << std::endl;
    const auto* i = infeasible.back().mInterval.get_internal();
    if (i->is_point)
    {
      sample =
          value_between(&i->a, true, Value::plus_infty().get_internal(), true);
    }
    else
    {
      sample = value_between(
          &i->b, !i->b_open, Value::plus_infty().get_internal(), true);
    }
    return true;
  }
  return false;
}

void render(std::ostream& os, const Value& val, bool approx_from_below = true)
{
  const lp_value_t* v = val.get_internal();
  if (v->type == LP_VALUE_INTEGER)
  {
    const poly::Integer& i = as_integer(val);
    if (sgn(i) < 0)
    {
      os << "(- " << poly::abs(i) << ")";
    }
    else
    {
      os << i;
    }
  }
  else if (v->type == LP_VALUE_RATIONAL)
  {
    const poly::Integer& n = numerator(as_rational(val));
    const poly::Integer& d = denominator(as_rational(val));
    if (sgn(as_rational(val)) < 0)
    {
      os << "(- (/ " << abs(n) << " " << d << "))";
    }
    else
    {
      os << "(/ " << n << " " << d << ")";
    }
  }
  else if (v->type == LP_VALUE_DYADIC_RATIONAL)
  {
    poly::Integer n = numerator(as_dyadic_rational(val));
    poly::Integer d = denominator(as_dyadic_rational(val));
    if (sgn(as_dyadic_rational(val)) < 0)
    {
      os << "(- (/ " << n << " " << d << "))";
    }
    else
    {
      os << "(/ " << n << " " << d << ")";
    }
  }
  else if (v->type == LP_VALUE_ALGEBRAIC)
  {
    const poly::AlgebraicNumber& an = as_algebraic_number(val);
    for (size_t i = 0; i < 10; ++i)
    {
      refine_const(an);
    }
    if (v->value.a.I.is_point)
    {
      Value value;
      lp_value_construct(
          value.get_internal(), LP_VALUE_DYADIC_RATIONAL, &v->value.a.I.a);
      render(os, value);
    }
    else
    {
      if (approx_from_below)
      {
        Value value;
        lp_value_construct(
            value.get_internal(), LP_VALUE_DYADIC_RATIONAL, &v->value.a.I.a);
        render(os, value);
      }
      else
      {
        Value value;
        lp_value_construct(
            value.get_internal(), LP_VALUE_DYADIC_RATIONAL, &v->value.a.I.b);
        render(os, value);
      }
    }
  }
  else
  {
    std::cout << "Skipping " << val << std::endl;
  }
}

void render(std::ostream& os, const Variable& v, const Interval& interval)
{
  const lp_interval_t* i = interval.get_internal();
  if (i->is_point)
  {
    os << "(assert (= " << v << " ";
    render(os, Value(get_lower(interval)));
    os << "))" << std::endl;
  }
  else
  {
    if (i->a.type != LP_VALUE_MINUS_INFINITY)
    {
      os << "(assert (< ";
      render(os, Value(get_lower(interval)), false);
      os << " " << v << "))" << std::endl;
    }
    if (i->b.type != LP_VALUE_PLUS_INFINITY)
    {
      os << "(assert (< " << v << " ";
      render(os, Value(get_upper(interval)), true);
      os << "))" << std::endl;
    }
  }
}

void CDCACDebugger::check_interval(const Assignment& a,
                                   const Variable& variable,
                                   const CACInterval& i)
{
  ++mCheckCounter;

  std::cout << "Writing interval to cac-debug-" + std::to_string(mCheckCounter)
                   + ".smt2"
            << std::endl;

  std::ofstream out("cac-debug-" + std::to_string(mCheckCounter) + ".smt2");
  out << "(set-logic QF_NRA)" << std::endl;
  for (const auto& v : mVariables)
  {
    out << "(declare-fun " << v << " () Real)" << std::endl;
  }
  out << "; Constraints used as origins" << std::endl;
  for (const auto& o : i.mOrigins)
  {
    out << "(assert " << o << ")" << std::endl;
  }
  out << "; Current assignment" << std::endl;
  for (const auto& v : mVariables)
  {
    if (a.has(v))
    {
      out << "(assert (= " << v << " ";
      render(out, a.get(v));
      out << "))" << std::endl;
    }
  }
  out << "; Excluded interval for " << variable << std::endl;
  render(out, variable, i.mInterval);
  out << "(check-sat)" << std::endl;
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4