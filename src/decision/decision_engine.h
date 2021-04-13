/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Decision engine.
 */

#include "cvc4_private.h"

#ifndef CVC5__DECISION__DECISION_ENGINE_H
#define CVC5__DECISION__DECISION_ENGINE_H

#include "base/output.h"
#include "context/cdo.h"
#include "decision/decision_strategy.h"
#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"
#include "util/result.h"

using namespace cvc5::prop;
using namespace cvc5::decision;

namespace cvc5 {

class DecisionEngine {

  // PropEngine* d_propEngine;
  CnfStream* d_cnfStream;
  CDCLTSatSolverInterface* d_satSolver;

  context::Context* d_satContext;
  context::UserContext* d_userContext;

  // Does decision engine know the answer?
  context::CDO<SatValue> d_result;

  // Disable creating decision engine without required parameters
  DecisionEngine();

  // init/shutdown state
  unsigned d_engineState;    // 0=pre-init; 1=init,pre-shutdown; 2=shutdown
  /** Pointer to resource manager for associated SmtEngine */
  ResourceManager* d_resourceManager;

 public:
  // Necessary functions

  /** Constructor */
  DecisionEngine(context::Context* sc,
                 context::UserContext* uc,
                 ResourceManager* rm);

  /** Destructor, currently does nothing */
  ~DecisionEngine() {
    Trace("decision") << "Destroying decision engine" << std::endl;
  }

  void setSatSolver(CDCLTSatSolverInterface* ss)
  {
    // setPropEngine should not be called more than once
    Assert(d_satSolver == NULL);
    Assert(ss != NULL);
    d_satSolver = ss;
  }

  void setCnfStream(CnfStream* cs) {
    // setPropEngine should not be called more than once
    Assert(d_cnfStream == NULL);
    Assert(cs != NULL);
    d_cnfStream = cs;
  }

  /* Enables decision strategy based on options. */
  void init();

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system.
   */
  void shutdown();

  // Interface for External World to use our services

  /** Gets the next decision based on strategies that are enabled */
  SatLiteral getNext(bool& stopSearch);

  /** Is the DecisionEngine in a state where it has solved everything? */
  bool isDone() {
    Trace("decision") << "DecisionEngine::isDone() returning "
                      << (d_result != SAT_VALUE_UNKNOWN)
                      << (d_result != SAT_VALUE_UNKNOWN ? "true" : "false")
                      << std::endl;
    return (d_result != SAT_VALUE_UNKNOWN);
  }

  /** */
  Result getResult() {
    switch(d_result.get()) {
    case SAT_VALUE_TRUE: return Result(Result::SAT);
    case SAT_VALUE_FALSE: return Result(Result::UNSAT);
    case SAT_VALUE_UNKNOWN: return Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    default: Assert(false) << "d_result is garbage";
    }
    return Result();
  }

  /** */
  void setResult(SatValue val) {
    d_result = val;
  }

  // External World helping us help the Strategies

  /**
   * Notify this class that assertion is an (input) assertion, not corresponding
   * to a skolem definition.
   */
  void addAssertion(TNode assertion);
  /**
   * Notify this class  that lem is the skolem definition for skolem, which is
   * a part of the current assertions.
   */
  void addSkolemDefinition(TNode lem, TNode skolem);

  // Interface for Strategies to use stuff stored in Decision Engine
  // (which was possibly requested by them on initialization)

  // Interface for Strategies to get information about External World

  bool hasSatLiteral(TNode n) {
    return d_cnfStream->hasLiteral(n);
  }
  SatLiteral getSatLiteral(TNode n) {
    return d_cnfStream->getLiteral(n);
  }
  SatValue getSatValue(SatLiteral l) {
    return d_satSolver->value(l);
  }
  SatValue getSatValue(TNode n) {
    return getSatValue(getSatLiteral(n));
  }
  Node getNode(SatLiteral l) {
    return d_cnfStream->getNode(l);
  }

 private:
  /** The ITE decision strategy we have allocated */
  std::unique_ptr<ITEDecisionStrategy> d_enabledITEStrategy;
};/* DecisionEngine class */

}  // namespace cvc5

#endif /* CVC5__DECISION__DECISION_ENGINE_H */
