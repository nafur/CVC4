/*********************                                                        */
/*! \file theory_proxy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "prop/theory_proxy.h"

#include "context/context.h"
#include "decision/decision_engine.h"
#include "options/decision_options.h"
#include "options/smt_options.h"
#include "proof/cnf_proof.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "util/statistics_registry.h"

namespace cvc5 {
namespace prop {

TheoryProxy::TheoryProxy(PropEngine* propEngine,
                         TheoryEngine* theoryEngine,
                         DecisionEngine* decisionEngine,
                         context::Context* context,
                         context::UserContext* userContext,
                         ProofNodeManager* pnm)
    : d_propEngine(propEngine),
      d_cnfStream(nullptr),
      d_decisionEngine(decisionEngine),
      d_theoryEngine(theoryEngine),
      d_queue(context),
      d_tpp(*theoryEngine, userContext, pnm),
      d_skdm(new SkolemDefManager(context, userContext))
{
}

TheoryProxy::~TheoryProxy() {
  /* nothing to do for now */
}

void TheoryProxy::finishInit(CnfStream* cnfStream) { d_cnfStream = cnfStream; }

void TheoryProxy::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  d_theoryEngine->notifyPreprocessedAssertions(assertions);
  for (const Node& assertion : assertions)
  {
    d_decisionEngine->addAssertion(assertion);
  }
}

void TheoryProxy::notifyAssertion(Node lem, TNode skolem)
{
  if (skolem.isNull())
  {
    d_decisionEngine->addAssertion(lem);
  }
  else
  {
    d_skdm->notifySkolemDefinition(skolem, lem);
    d_decisionEngine->addSkolemDefinition(lem, skolem);
  }
}

void TheoryProxy::variableNotify(SatVariable var) {
  d_theoryEngine->preRegister(getNode(SatLiteral(var)));
}

void TheoryProxy::theoryCheck(theory::Theory::Effort effort) {
  while (!d_queue.empty()) {
    TNode assertion = d_queue.front();
    d_queue.pop();
    d_theoryEngine->assertFact(assertion);
  }
  d_theoryEngine->check(effort);
}

void TheoryProxy::theoryPropagate(std::vector<SatLiteral>& output) {
  // Get the propagated literals
  std::vector<TNode> outputNodes;
  d_theoryEngine->getPropagatedLiterals(outputNodes);
  for (unsigned i = 0, i_end = outputNodes.size(); i < i_end; ++ i) {
    Debug("prop-explain") << "theoryPropagate() => " << outputNodes[i] << std::endl;
    output.push_back(d_cnfStream->getLiteral(outputNodes[i]));
  }
}

void TheoryProxy::explainPropagation(SatLiteral l, SatClause& explanation) {
  TNode lNode = d_cnfStream->getNode(l);
  Debug("prop-explain") << "explainPropagation(" << lNode << ")" << std::endl;

  theory::TrustNode tte = d_theoryEngine->getExplanation(lNode);
  Node theoryExplanation = tte.getNode();
  if (cvc5::options::produceProofs())
  {
    d_propEngine->getProofCnfStream()->convertPropagation(tte);
  }
  else if (options::unsatCores())
  {
    ProofManager::getCnfProof()->pushCurrentAssertion(theoryExplanation);
  }
  Debug("prop-explain") << "explainPropagation() => " << theoryExplanation
                        << std::endl;
  explanation.push_back(l);
  if (theoryExplanation.getKind() == kind::AND)
  {
    for (const Node& n : theoryExplanation)
    {
      explanation.push_back(~d_cnfStream->getLiteral(n));
    }
  }
  else
  {
    explanation.push_back(~d_cnfStream->getLiteral(theoryExplanation));
  }
  if (Trace.isOn("sat-proof"))
  {
    std::stringstream ss;
    ss << "TheoryProxy::explainPropagation: clause for lit is ";
    for (unsigned i = 0, size = explanation.size(); i < size; ++i)
    {
      ss << explanation[i] << " [" << d_cnfStream->getNode(explanation[i])
         << "] ";
    }
    Trace("sat-proof") << ss.str() << "\n";
  }
}

void TheoryProxy::enqueueTheoryLiteral(const SatLiteral& l) {
  Node literalNode = d_cnfStream->getNode(l);
  Debug("prop") << "enqueueing theory literal " << l << " " << literalNode << std::endl;
  Assert(!literalNode.isNull());
  d_queue.push(literalNode);
}

SatLiteral TheoryProxy::getNextTheoryDecisionRequest() {
  TNode n = d_theoryEngine->getNextDecisionRequest();
  return n.isNull() ? undefSatLiteral : d_cnfStream->getLiteral(n);
}

SatLiteral TheoryProxy::getNextDecisionEngineRequest(bool &stopSearch) {
  Assert(d_decisionEngine != NULL);
  Assert(stopSearch != true);
  SatLiteral ret = d_decisionEngine->getNext(stopSearch);
  if(stopSearch) {
    Trace("decision") << "  ***  Decision Engine stopped search *** " << std::endl;
  }
  return options::decisionStopOnly() ? undefSatLiteral : ret;
}

bool TheoryProxy::theoryNeedCheck() const {
  return d_theoryEngine->needCheck();
}

TNode TheoryProxy::getNode(SatLiteral lit) {
  return d_cnfStream->getNode(lit);
}

void TheoryProxy::notifyRestart() {
  d_propEngine->spendResource(ResourceManager::Resource::RestartStep);
  d_theoryEngine->notifyRestart();
}

void TheoryProxy::spendResource(ResourceManager::Resource r)
{
  d_theoryEngine->spendResource(r);
}

bool TheoryProxy::isDecisionRelevant(SatVariable var) { return true; }

bool TheoryProxy::isDecisionEngineDone() {
  return d_decisionEngine->isDone();
}

SatValue TheoryProxy::getDecisionPolarity(SatVariable var) {
  return SAT_VALUE_UNKNOWN;
}

CnfStream* TheoryProxy::getCnfStream() { return d_cnfStream; }

theory::TrustNode TheoryProxy::preprocessLemma(
    theory::TrustNode trn,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  return d_tpp.preprocessLemma(trn, newLemmas, newSkolems);
}

theory::TrustNode TheoryProxy::preprocess(
    TNode node,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  return d_tpp.preprocess(node, newLemmas, newSkolems);
}

theory::TrustNode TheoryProxy::removeItes(
    TNode node,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  RemoveTermFormulas& rtf = d_tpp.getRemoveTermFormulas();
  return rtf.run(node, newLemmas, newSkolems, true);
}

void TheoryProxy::getSkolems(TNode node,
                             std::vector<Node>& skAsserts,
                             std::vector<Node>& sks)
{
  std::unordered_set<Node, NodeHashFunction> skolems;
  d_skdm->getSkolems(node, skolems);
  for (const Node& k : skolems)
  {
    sks.push_back(k);
    skAsserts.push_back(d_skdm->getDefinitionForSkolem(k));
  }
}

void TheoryProxy::preRegister(Node n) { d_theoryEngine->preRegister(n); }

}  // namespace prop
}  // namespace cvc5
