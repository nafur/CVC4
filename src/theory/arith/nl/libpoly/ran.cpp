#include "ran.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace libpoly {

RAN::RAN(UPolynomial&& poly, const DyadicInterval& i)
{
  lp_algebraic_number_construct(&mValue, poly.release(), i.get());
}
RAN::RAN(const UPolynomial& poly, const DyadicInterval& i)
{
  lp_algebraic_number_construct(&mValue, UPolynomial(poly).release(), i.get());
}
RAN::RAN(const lp_algebraic_number_t& ran)
{
  lp_algebraic_number_construct_copy(&mValue, &ran);
}
RAN::RAN(const RAN& ran)
{
  lp_algebraic_number_construct_copy(&mValue, ran.get());
}
RAN::RAN(RAN&& ran)
{
  lp_algebraic_number_construct_zero(&mValue);
  lp_algebraic_number_swap(&mValue, ran.get());
}
RAN::~RAN() { lp_algebraic_number_destruct(&mValue); }
RAN& RAN::operator=(RAN r)
{
  std::swap(mValue, r.mValue);
  return *this;
}

RAN::operator Value() const
{
  return Value(lp_value_new(lp_value_type_t::LP_VALUE_ALGEBRAIC, &mValue));
}

lp_algebraic_number_t* RAN::get() { return &mValue; }
const lp_algebraic_number_t* RAN::get() const { return &mValue; }

std::ostream& operator<<(std::ostream& os, const RAN& v)
{
  return os << lp_algebraic_number_to_string(v.get());
}

bool operator==(const RAN& lhs, const RAN& rhs)
{
  return lp_algebraic_number_cmp(lhs.get(), rhs.get()) == 0;
}
bool operator==(const RAN& lhs, const Integer& rhs)
{
  return lp_algebraic_number_cmp_integer(lhs.get(), rhs.get()) == 0;
}
bool operator==(const Integer& lhs, const RAN& rhs)
{
  return lp_algebraic_number_cmp_integer(rhs.get(), lhs.get()) == 0;
}

std::vector<RAN> isolate_real_roots(const UPolynomial& p)
{
  lp_algebraic_number_t* roots = new lp_algebraic_number_t[degree(p)];
  std::size_t roots_size;
  lp_upolynomial_roots_isolate(p.get(), roots, &roots_size);
  std::vector<RAN> res;
  for (std::size_t i = 0; i < roots_size; ++i)
  {
    res.emplace_back(roots[i]);
  }
  for (std::size_t i = 0; i < roots_size; ++i)
  {
    lp_algebraic_number_destruct(&roots[i]);
  }
  delete[] roots;
  return res;
}

std::vector<Value> isolate_real_roots(const Polynomial& p, const Assignment& a)
{
  lp_value_t* roots = new lp_value_t[degree(p)];
  std::size_t roots_size;
  lp_polynomial_roots_isolate(p.get(), a.get(), roots, &roots_size);
  std::vector<Value> res;
  for (std::size_t i = 0; i < roots_size; ++i)
  {
    res.emplace_back(lp_value_new_copy(&roots[i]));
  }
  for (std::size_t i = 0; i < roots_size; ++i)
  {
    lp_value_destruct(&roots[i]);
  }
  delete[] roots;
  return res;
}

}  // namespace libpoly
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
