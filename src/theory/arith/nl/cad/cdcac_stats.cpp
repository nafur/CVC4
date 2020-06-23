#include "cdcac_stats.h"

#include "theory_call_exporter.h"
#include "util/poly_util.h"
#include "variable_ordering.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

NRAStatistics::NRAStatistics(std::string name)
    : num_variables(name + "::num_variables", 0),
      num_polynomials(name + "::num_polynomials", 0),
      max_tdegree(name + "::max_tdegree", 0),
      max_degree_a(name + "::max_degree_a", 0),
      max_degree_b(name + "::max_degree_b", 0),
      max_degree_c(name + "::max_degree_c", 0),
      max_degree_x(name + "::max_degree_x", 0),
      max_degree_y(name + "::max_degree_y", 0),
      max_degree_z(name + "::max_degree_z", 0),
      perc_poly_contain_a(name + "::perc_poly_contain_a"),
      perc_poly_contain_b(name + "::perc_poly_contain_b"),
      perc_poly_contain_c(name + "::perc_poly_contain_c"),
      perc_poly_contain_x(name + "::perc_poly_contain_x"),
      perc_poly_contain_y(name + "::perc_poly_contain_y"),
      perc_poly_contain_z(name + "::perc_poly_contain_z"),
      perc_monomial_contain_a(name + "::perc_monomial_contain_a"),
      perc_monomial_contain_b(name + "::perc_monomial_contain_b"),
      perc_monomial_contain_c(name + "::perc_monomial_contain_c"),
      perc_monomial_contain_x(name + "::perc_monomial_contain_x"),
      perc_monomial_contain_y(name + "::perc_monomial_contain_y"),
      perc_monomial_contain_z(name + "::perc_monomial_contain_z")
{
  smtStatisticsRegistry()->registerStat(&num_variables);
  smtStatisticsRegistry()->registerStat(&num_polynomials);
  smtStatisticsRegistry()->registerStat(&max_tdegree);
  smtStatisticsRegistry()->registerStat(&max_degree_a);
  smtStatisticsRegistry()->registerStat(&max_degree_b);
  smtStatisticsRegistry()->registerStat(&max_degree_c);
  smtStatisticsRegistry()->registerStat(&max_degree_x);
  smtStatisticsRegistry()->registerStat(&max_degree_y);
  smtStatisticsRegistry()->registerStat(&max_degree_z);
  smtStatisticsRegistry()->registerStat(&perc_poly_contain_a);
  smtStatisticsRegistry()->registerStat(&perc_poly_contain_b);
  smtStatisticsRegistry()->registerStat(&perc_poly_contain_c);
  smtStatisticsRegistry()->registerStat(&perc_poly_contain_x);
  smtStatisticsRegistry()->registerStat(&perc_poly_contain_y);
  smtStatisticsRegistry()->registerStat(&perc_poly_contain_z);
  smtStatisticsRegistry()->registerStat(&perc_monomial_contain_a);
  smtStatisticsRegistry()->registerStat(&perc_monomial_contain_b);
  smtStatisticsRegistry()->registerStat(&perc_monomial_contain_c);
  smtStatisticsRegistry()->registerStat(&perc_monomial_contain_x);
  smtStatisticsRegistry()->registerStat(&perc_monomial_contain_y);
  smtStatisticsRegistry()->registerStat(&perc_monomial_contain_z);
}

NRAStatistics::~NRAStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&num_variables);
  smtStatisticsRegistry()->unregisterStat(&num_polynomials);
  smtStatisticsRegistry()->unregisterStat(&max_tdegree);
  smtStatisticsRegistry()->unregisterStat(&max_degree_a);
  smtStatisticsRegistry()->unregisterStat(&max_degree_b);
  smtStatisticsRegistry()->unregisterStat(&max_degree_c);
  smtStatisticsRegistry()->unregisterStat(&max_degree_x);
  smtStatisticsRegistry()->unregisterStat(&max_degree_y);
  smtStatisticsRegistry()->unregisterStat(&max_degree_z);
  smtStatisticsRegistry()->unregisterStat(&perc_poly_contain_a);
  smtStatisticsRegistry()->unregisterStat(&perc_poly_contain_b);
  smtStatisticsRegistry()->unregisterStat(&perc_poly_contain_c);
  smtStatisticsRegistry()->unregisterStat(&perc_poly_contain_x);
  smtStatisticsRegistry()->unregisterStat(&perc_poly_contain_y);
  smtStatisticsRegistry()->unregisterStat(&perc_poly_contain_z);
  smtStatisticsRegistry()->unregisterStat(&perc_monomial_contain_a);
  smtStatisticsRegistry()->unregisterStat(&perc_monomial_contain_b);
  smtStatisticsRegistry()->unregisterStat(&perc_monomial_contain_c);
  smtStatisticsRegistry()->unregisterStat(&perc_monomial_contain_x);
  smtStatisticsRegistry()->unregisterStat(&perc_monomial_contain_y);
  smtStatisticsRegistry()->unregisterStat(&perc_monomial_contain_z);
}

void NRAStatistics::make_stats(const Constraints::ConstraintVector& constraints)
{
  auto data = cad::collect_information(constraints, true);

  poly_utils::VariableInformation totals = data.back();
  data.pop_back();

  num_polynomials.maxAssign(constraints.size());
  num_variables.maxAssign(data.size());

  std::sort(data.begin(),
            data.end(),
            [](const poly_utils::VariableInformation& a,
               const poly_utils::VariableInformation& b) {
              return a.max_degree > b.max_degree;
            });
  if (data.size() > 0) max_degree_a.maxAssign(data[0].max_degree);
  if (data.size() > 1) max_degree_b.maxAssign(data[1].max_degree);
  if (data.size() > 2) max_degree_c.maxAssign(data[2].max_degree);
  if (data.size() > 2) max_degree_x.maxAssign(data[data.size() - 3].max_degree);
  if (data.size() > 1) max_degree_y.maxAssign(data[data.size() - 2].max_degree);
  if (data.size() > 0) max_degree_z.maxAssign(data[data.size() - 1].max_degree);

  std::sort(data.begin(),
            data.end(),
            [](const poly_utils::VariableInformation& a,
               const poly_utils::VariableInformation& b) {
              return a.num_polynomials > b.num_polynomials;
            });
  double npolys = totals.num_polynomials;
  if (data.size() > 0)
    perc_poly_contain_a.addEntry(data[0].num_polynomials / npolys);
  if (data.size() > 1)
    perc_poly_contain_b.addEntry(data[1].num_polynomials / npolys);
  if (data.size() > 2)
    perc_poly_contain_c.addEntry(data[2].num_polynomials / npolys);
  if (data.size() > 2)
    perc_poly_contain_x.addEntry(data[data.size() - 3].num_polynomials
                                 / npolys);
  if (data.size() > 1)
    perc_poly_contain_y.addEntry(data[data.size() - 2].num_polynomials
                                 / npolys);
  if (data.size() > 0)
    perc_poly_contain_z.addEntry(data[data.size() - 1].num_polynomials
                                 / npolys);

  std::sort(data.begin(),
            data.end(),
            [](const poly_utils::VariableInformation& a,
               const poly_utils::VariableInformation& b) {
              return a.num_terms > b.num_terms;
            });
  double nterms = totals.num_terms;
  if (data.size() > 0)
    perc_monomial_contain_a.addEntry(data[0].num_terms / nterms);
  if (data.size() > 1)
    perc_monomial_contain_b.addEntry(data[1].num_terms / nterms);
  if (data.size() > 2)
    perc_monomial_contain_c.addEntry(data[2].num_terms / nterms);
  if (data.size() > 2)
    perc_monomial_contain_x.addEntry(data[data.size() - 3].num_terms / nterms);
  if (data.size() > 1)
    perc_monomial_contain_y.addEntry(data[data.size() - 2].num_terms / nterms);
  if (data.size() > 0)
    perc_monomial_contain_z.addEntry(data[data.size() - 1].num_terms / nterms);

  for (const auto& c : constraints)
  {
    const auto& p = std::get<0>(c);
    max_tdegree.maxAssign(poly_utils::total_degree(p));
  }
}

void NRAStatistics::as_json(std::ostream& os, const std::string& prefix) const
{
  os << prefix << "{" << std::endl;
  os << prefix << "\t\"num_variables\": " << num_variables.getData() << "," << std::endl;
  os << prefix << "\t\"num_polynomials\": " << num_polynomials.getData() << "," << std::endl;
  os << prefix << "\t\"max_tdegree\": " << max_tdegree.getData() << "," << std::endl;
  os << prefix << "\t\"max_degree_a\": " << max_degree_a.getData() << "," << std::endl;
  os << prefix << "\t\"max_degree_b\": " << max_degree_b.getData() << "," << std::endl;
  os << prefix << "\t\"max_degree_c\": " << max_degree_c.getData() << "," << std::endl;
  os << prefix << "\t\"max_degree_x\": " << max_degree_x.getData() << "," << std::endl;
  os << prefix << "\t\"max_degree_y\": " << max_degree_y.getData() << "," << std::endl;
  os << prefix << "\t\"max_degree_z\": " << max_degree_z.getData() << "," << std::endl;
  os << prefix << "\t\"perc_poly_contain_a\": " << perc_poly_contain_a.getData() << "," << std::endl;
  os << prefix << "\t\"perc_poly_contain_b\": " << perc_poly_contain_b.getData() << "," << std::endl;
  os << prefix << "\t\"perc_poly_contain_c\": " << perc_poly_contain_c.getData() << "," << std::endl;
  os << prefix << "\t\"perc_poly_contain_x\": " << perc_poly_contain_x.getData() << "," << std::endl;
  os << prefix << "\t\"perc_poly_contain_y\": " << perc_poly_contain_y.getData() << "," << std::endl;
  os << prefix << "\t\"perc_poly_contain_z\": " << perc_poly_contain_z.getData() << "," << std::endl;
  os << prefix << "\t\"perc_monomial_contain_a\": " << perc_monomial_contain_a.getData() << "," << std::endl;
  os << prefix << "\t\"perc_monomial_contain_b\": " << perc_monomial_contain_b.getData() << "," << std::endl;
  os << prefix << "\t\"perc_monomial_contain_c\": " << perc_monomial_contain_c.getData() << "," << std::endl;
  os << prefix << "\t\"perc_monomial_contain_x\": " << perc_monomial_contain_x.getData() << "," << std::endl;
  os << prefix << "\t\"perc_monomial_contain_y\": " << perc_monomial_contain_y.getData() << "," << std::endl;
  os << prefix << "\t\"perc_monomial_contain_z\": " << perc_monomial_contain_z.getData() << std::endl;
  os << prefix << "}" << std::endl;
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4