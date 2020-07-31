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

#include "theory/arith/nl/cad_solver.h"

#include <poly/polyxx.h>

#include "inference.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/cad/cdcac.h"
#include "theory/arith/nl/poly_conversion.h"
#include "util/poly_util.h"
#include "cad/theory_call_exporter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

// #define EXPORT_THEORY_CALLS

bool CadSolver::construct_model()
{
  for (const auto& v : mCAC.getVariableOrdering())
  {
    Node variable = mCAC.getConstraints().varMapper()(v);
    Node value = value_to_node(mCAC.getModel().get(v), ran_variable);
    if (value.isConst())
    {
      d_model.addCheckModelSubstitution(variable, value);
    }
    else
    {
      d_model.addCheckModelWitness(variable, value);
    }
    Trace("cad-check") << "-> " << v << " = " << value << std::endl;
  }
  return true;
}

CadSolver::CadSolver(TheoryArith& containing, NlModel& model)
    : ran_variable(NodeManager::currentNM()->mkSkolem("__z", NodeManager::currentNM()->realType(), "", NodeManager::SKOLEM_EXACT_NAME)), d_containing(containing), d_model(model)
{
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
      if (std::find(false_asserts.begin(), false_asserts.end(), a)
          != false_asserts.end())
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
    mCAC.getConstraints().addConstraint(a);
  }
#ifdef EXPORT_THEORY_CALLS
  static std::size_t theory_calls = 0;
  ++theory_calls;
  cad::NRAFeatures stats(mCAC.get_constraints().get_constraints());
  cad::export_theory_call(theory_calls, assertions, stats);
#endif
  mCAC.computeVariableOrdering();
  mCAC.retrieve_initial_assignment(d_model, ran_variable);
}

std::vector<NlLemma> CadSolver::checkInitialRefine()
{
  Chat() << "CadSolver::checkInitialRefine" << std::endl;
  return {};
}

std::vector<NlLemma> CadSolver::checkFullRefine()
{
  Notice() << "CadSolver::checkFullRefine" << std::endl;
#ifdef EXPORT_THEORY_CALLS
  std::cout << "Abort solving as we only export theory calls." << std::endl;
  return {};
#endif

  return check_full();
}

void CadSolver::preprocessAssertionsCheckModel(std::vector<Node>& assertions)
{
  if (found_satisfiability)
  {
    Notice() << "Storing " << mCAC.getModel() << std::endl;
    Trace("cdcac") << "Storing " << mCAC.getModel() << std::endl;
    construct_model();
    assertions.clear();
  }
}

std::vector<NlLemma> CadSolver::check_full()
{
  std::vector<NlLemma> lems;
  auto covering = mCAC.getUnsatCover();
  if (covering.empty())
  {
    found_satisfiability = true;
    Notice() << "SAT: " << mCAC.getModel() << std::endl;
  }
  else
  {
    found_satisfiability = false;
    auto mis = collectConstraints(covering);
    Notice() << "Collected MIS: " << mis << std::endl;
    auto* nm = NodeManager::currentNM();
    for (auto& n : mis)
    {
      n = n.negate();
    }
    Assert(!mis.empty()) << "Infeasible subset can not be empty";
    if (mis.size() == 1)
    {
      lems.emplace_back(mis.front(), Inference::CAD_CONFLICT);
    }
    else
    {
      lems.emplace_back(nm->mkNode(Kind::OR, mis), Inference::CAD_CONFLICT);
    }
    Notice() << "UNSAT with MIS: " << lems.back().d_lemma << std::endl;
  }
  return lems;
}

std::vector<NlLemma> CadSolver::check_partial()
{
  std::vector<NlLemma> lems;
  auto covering = mCAC.getUnsatCover(0, true);
  if (covering.empty())
  {
    found_satisfiability = true;
    Notice() << "SAT: " << mCAC.getModel() << std::endl;
  }
  else
  {
    for (const auto& interval: covering) {
      Node first_var = mCAC.getConstraints().varMapper()(mCAC.getVariableOrdering()[0]);
      Node lemma = excluding_interval_to_lemma(first_var, interval.d_interval);
      lems.emplace_back(lemma, Inference::CAD_EXCLUDED_INTERVAL);
    }
  }
  return lems;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
