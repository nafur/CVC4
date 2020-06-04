#include "projections.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

using namespace libpoly;

void reduce_projection_polynomials(std::vector<Polynomial>& polys)
{
  std::sort(polys.begin(), polys.end());
  auto it = std::unique(polys.begin(), polys.end());
  polys.erase(it, polys.end());
}

void add_polynomial(std::vector<Polynomial>& polys, const Polynomial& poly)
{
  for (const auto& p : square_free_factors(poly))
  {
    if (is_constant(p)) continue;
    polys.emplace_back(p);
    polys.back().simplify();
  }
}

void add_polynomials(std::vector<Polynomial>& polys, const std::vector<Polynomial>& p)
{
  for (const auto& q: p) add_polynomial(polys, q);
}

std::vector<Polynomial> projection_mccallum(
    const std::vector<Polynomial>& polys)
{
  std::vector<Polynomial> res;

  for (const auto& p : polys)
  {
    for (const auto& coeff : coefficients(p))
    {
      add_polynomial(res, coeff);
    }
    add_polynomial(res, discriminant(p));
  }
  for (std::size_t i = 0; i < polys.size(); ++i)
  {
    for (std::size_t j = i + 1; j < polys.size(); ++j)
    {
      add_polynomial(res, resultant(polys[i], polys[j]));
    }
  }

  reduce_projection_polynomials(res);
  return res;
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
