/*********************                                                        */
/*! \file cad_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of new non-linear solver
 **/

//#include <poly/upolynomial.h>

#include <poly/polyxx.h>

#include "theory/arith/nl/cad_solver.h"
#include "theory/arith/nl/cad/cdcac.h"
#include "theory/arith/nl/poly_conversion.h"

#include "util/poly_util.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

  bool CadSolver::assign_model_variable(const Node& variable, const poly::Value& value) const {
    auto* nm = NodeManager::currentNM();
    switch (value.get_internal()->type) {
      case LP_VALUE_INTEGER: {
        d_model.addCheckModelSubstitution(
          variable,
          nm->mkConst(Rational(poly_utils::to_integer(poly::to_integer(value))))
        );
        return true;
      }
      case LP_VALUE_RATIONAL: {
        d_model.addCheckModelSubstitution(
          variable,
          nm->mkConst(poly_utils::to_rational(poly::to_rational(value)))
        );
        return true;
      }
      case LP_VALUE_DYADIC_RATIONAL: {
        d_model.addCheckModelSubstitution(
          variable,
          nm->mkConst(poly_utils::to_rational(poly::to_dyadic_rational(value)))
        );
        return true;
      }
      case LP_VALUE_ALGEBRAIC: {
        //Trace("cad-check") << value << " is an algebraic" << std::endl;
        // For the sake of it...
        const poly::AlgebraicNumber& ran = poly::to_algebraic_number(value);
        const lp_algebraic_number_t& a = value.get_internal()->value.a;
        //for (std::size_t i = 0; i < 10; ++i) {
        //  lp_algebraic_number_refine_const(&a);
        //}
        if (a.I.is_point) {
          d_model.addCheckModelSubstitution(
            variable,
            nm->mkConst(poly_utils::to_rational(*poly::detail::cast_from(&a.I.a)))
          );
        } else {
          Node poly = as_cvc_polynomial(poly::UPolynomial(lp_upolynomial_construct_copy(a.f)), variable);
          // Construct witness:
          // a.f(x) == 0  &&  a.I.a < x  &&  x < a.I.b
          Node witness = nm->mkNode(Kind::AND,
            nm->mkNode(Kind::EQUAL, poly, nm->mkConst(Rational(0))),
            nm->mkNode(Kind::LT,
              nm->mkConst(poly_utils::to_rational(get_lower_bound(ran))),
              variable
            ),
            nm->mkNode(Kind::LT,
              variable,
              nm->mkConst(poly_utils::to_rational(get_upper_bound(ran)))
            )
          );
          Trace("cad-check") << "Adding witness: " << witness << std::endl;
          d_model.addCheckModelWitness(variable, witness);
        }
        return true;
      }
      default: {
        Trace("cad-check") << value << " is weird" << std::endl;
        return false;
      }
    }
  }

  bool CadSolver::construct_model() {
    for (const auto& v: mCAC.get_variable_ordering()) {
      poly::Value val = mCAC.get_model().get(v);
      Node variable = mCAC.get_constraints().var_mapper()(v);
      if (assign_model_variable(variable, val)) {
        Trace("cad-check") << "-> " << v << " = " << val << std::endl;
      } else {
        Trace("cad-check") << "Failed to set " << v << " = " << val << std::endl;
      }
    }
    return true;
  }

CadSolver::CadSolver(TheoryArith& containing, NlModel& model)
    : d_containing(containing),
      d_model(model)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_neg_one = nm->mkConst(Rational(-1));
}

CadSolver::~CadSolver() {}

void CadSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  if (Trace.isOn("cad-check"))
  {
    Trace("cad-check") << "CadSolver::initLastCall" << std::endl;
    Trace("cad-check") << "* Assertions: " << std::endl;
    for (const Node& a : assertions)
    {
      Trace("cad-check") << "  " << a << std::endl;
      if (std::find(false_asserts.begin(),false_asserts.end(),a)!=false_asserts.end())
      {
        Trace("cad-check") << " (false in candidate model)" << std::endl;
      }
    }
    Trace("cad-check") << "* Extended terms: " << std::endl;
    for (const Node& t : xts)
    {
      Trace("cad-check") << "  " << t << std::endl;
    }
  }
  // store or process assertions
  mCAC.reset();
  for (const Node& a : assertions)
  {
    mCAC.get_constraints().add_constraint(a);
  }
  mCAC.compute_variable_ordering();
}

std::vector<NlLemma> CadSolver::checkInitialRefine()
{
  Chat() << "CadSolver::checkInitialRefine" << std::endl;
  std::vector<NlLemma> lems;
  
  // add lemmas corresponding to easy conflicts or refinements based on
  // the assertions/terms given in initLastCall.

  return lems;
}

std::vector<NlLemma> CadSolver::checkFullRefine()
{
  Notice() << "CadSolver::checkFullRefine" << std::endl;
  std::vector<NlLemma> lems;

  // Do full theory check here

  auto covering = mCAC.get_unsat_cover();
  if (covering.empty()) {
    found_satisfiability = true;
    Notice() << "SAT: " << mCAC.get_model() << std::endl;
  } else {
    found_satisfiability = false;
    auto mis = collect_constraints(covering);
    Notice() << "Collected MIS: " << mis << std::endl;
    auto* nm = NodeManager::currentNM();
    for (auto& n: mis) {
      n = n.negate();
    }
    Assert(!mis.empty()) << "Infeasible subset can not be empty";
    if (mis.size() == 1) {
      lems.emplace_back(mis.front());
    } else {
      lems.emplace_back(nm->mkNode(Kind::OR, mis));
    }
    Notice() << "UNSAT with MIS: " << lems.back().d_lemma << std::endl;
  } 
  
  return lems;
}

void CadSolver::preprocessAssertionsCheckModel(std::vector<Node>& assertions)
{
    if (found_satisfiability) {
      Notice() << "Storing " << mCAC.get_model() << std::endl;
      construct_model();
      assertions.clear();
    }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
