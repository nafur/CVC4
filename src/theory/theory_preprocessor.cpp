/*********************                                                        */
/*! \file theory_preprocessor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory preprocessor
 **/

#include "theory/theory_preprocessor.h"

#include "expr/lazy_proof.h"
#include "expr/skolem_manager.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

using namespace std;

namespace CVC4 {
namespace theory {

TheoryPreprocessor::TheoryPreprocessor(TheoryEngine& engine,
                                       context::UserContext* userContext,
                                       ProofNodeManager* pnm)
    : d_engine(engine),
      d_logicInfo(engine.getLogicInfo()),
      d_ppCache(userContext),
      d_rtfCache(userContext),
      d_tfr(userContext, pnm),
      d_tpg(pnm ? new TConvProofGenerator(
                      pnm,
                      userContext,
                      TConvPolicy::FIXPOINT,
                      TConvCachePolicy::NEVER,
                      "TheoryPreprocessor::preprocess_rewrite",
                      &d_iqtc)
                : nullptr),
      d_tpgRtf(pnm ? new TConvProofGenerator(pnm,
                                             userContext,
                                             TConvPolicy::FIXPOINT,
                                             TConvCachePolicy::NEVER,
                                             "TheoryPreprocessor::rtf",
                                             &d_iqtc)
                   : nullptr),
      d_tpgRew(pnm ? new TConvProofGenerator(pnm,
                                             userContext,
                                             TConvPolicy::ONCE,
                                             TConvCachePolicy::NEVER,
                                             "TheoryPreprocessor::pprew")
                   : nullptr),
      d_tspg(nullptr),
      d_lp(pnm ? new LazyCDProof(pnm,
                                 nullptr,
                                 userContext,
                                 "TheoryPreprocessor::LazyCDProof")
               : nullptr)
{
  if (isProofEnabled())
  {
    // Make the main term conversion sequence generator, which tracks up to
    // three conversions made in succession:
    // (1) rewriting
    // (2) theory preprocessing+rewriting
    // (3) term formula removal
    // (4) rewriting
    // Steps (2) and (4) use a common term conversion generator.
    std::vector<ProofGenerator*> ts;
    ts.push_back(d_tpgRew.get());
    ts.push_back(d_tpgRtf.get());
    ts.push_back(d_tpgRew.get());
    d_tspg.reset(new TConvSeqProofGenerator(
        pnm, ts, userContext, "TheoryPreprocessor::sequence"));
  }
}

TheoryPreprocessor::~TheoryPreprocessor() {}

TrustNode TheoryPreprocessor::preprocess(TNode node,
                                         std::vector<TrustNode>& newLemmas,
                                         std::vector<Node>& newSkolems)
{
  return preprocessInternal(node, newLemmas, newSkolems, true);
}

TrustNode TheoryPreprocessor::preprocessInternal(
    TNode node,
    std::vector<TrustNode>& newLemmas,
    std::vector<Node>& newSkolems,
    bool procLemmas)
{
  // In this method, all rewriting steps of node are stored in d_tpg.

  Trace("tpp-debug") << "TheoryPreprocessor::preprocess: start " << node
                     << std::endl;

  // We must rewrite before preprocessing, because some terms when rewritten
  // may introduce new terms that are not top-level and require preprocessing.
  // An example of this is (forall ((x Int)) (and (tail L) (P x))) which
  // rewrites to (and (tail L) (forall ((x Int)) (P x))). The subterm (tail L)
  // must be preprocessed as a child here.
  Node irNode = rewriteWithProof(node, d_tpgRew.get(), true);

  // run theory preprocessing
  TrustNode tpp = theoryPreprocess(irNode, newLemmas, newSkolems);
  Node ppNode = tpp.getNode();
  
  Node pprNode = rewriteWithProof(ppNode, d_tpgRew.get(), true);

  AlwaysAssert (Rewriter::rewrite(pprNode)==pprNode);
      TrustNode ttfr = d_tfr.run(pprNode, newLemmas, newSkolems, false);
      AlwaysAssert( ttfr.isNull()) << "Non-tfr: " << ppNode << std::endl;
      
  if (Trace.isOn("tpp-debug"))
  {
    if (node != irNode)
    {
      Trace("tpp-debug") << "after initial rewriting : " << irNode << std::endl;
    }
    if (irNode != ppNode)
    {
      Trace("tpp-debug") << "after preprocessing + rewriting and term formula removal : " << ppNode << std::endl;
    }
    if (ppNode != pprNode)
    {
      Trace("tpp-debug") << "after rewriting again : " << pprNode << std::endl;
    }
    Trace("tpp-debug") << "TheoryPreprocessor::preprocess: finish" << std::endl;
  }
  if (node == pprNode)
  {
    Trace("tpp-debug") << "...TheoryPreprocessor::preprocess returned no change"
                       << std::endl;
    // no change
    return TrustNode::null();
  }

  // Now, sequence the conversion steps if proofs are enabled.
  TrustNode tret;
  if (isProofEnabled())
  {
    std::vector<Node> cterms;
    cterms.push_back(node);
    cterms.push_back(irNode);
    cterms.push_back(ppNode);
    cterms.push_back(pprNode);
    // We have that:
    // node -> ppNode via preprocessing + rewriting
    // ppNode -> rtfNode via term formula removal
    // rtfNode -> retNode via rewriting
    tret = d_tspg->mkTrustRewriteSequence(cterms);
    tret.debugCheckClosed("tpp-debug", "TheoryPreprocessor::lemma_ret");
  }
  else
  {
    tret = TrustNode::mkTrustRewrite(node, pprNode, nullptr);
  }

  // now, rewrite the lemmas
  Trace("tpp-debug") << "TheoryPreprocessor::preprocess: process lemmas"
                     << std::endl;
  for (size_t i = 0, lsize = newLemmas.size(); i < lsize; ++i)
  {
    // get the trust node to process
    TrustNode trn = newLemmas[i];
    trn.debugCheckClosed(
        "tpp-debug", "TheoryPreprocessor::lemma_new_initial", false);
    Assert(trn.getKind() == TrustNodeKind::LEMMA);
    Node assertion = trn.getNode();
    // rewrite, which is independent of d_tpg, since additional lemmas
    // are justified separately.
    Node rewritten = Rewriter::rewrite(assertion);
    if (assertion != rewritten)
    {
      if (isProofEnabled())
      {
        Assert(d_lp != nullptr);
        // store in the lazy proof
        d_lp->addLazyStep(assertion,
                          trn.getGenerator(),
                          PfRule::THEORY_PREPROCESS_LEMMA,
                          true,
                          "TheoryPreprocessor::rewrite_lemma_new");
        d_lp->addStep(rewritten,
                      PfRule::MACRO_SR_PRED_TRANSFORM,
                      {assertion},
                      {rewritten});
      }
      newLemmas[i] = TrustNode::mkTrustLemma(rewritten, d_lp.get());
    }
    Assert(!isProofEnabled() || newLemmas[i].getGenerator() != nullptr);
    newLemmas[i].debugCheckClosed("tpp-debug", "TheoryPreprocessor::lemma_new");
  }
  Trace("tpp-debug") << "...TheoryPreprocessor::preprocess returned "
                     << tret.getNode() << std::endl;
  if (procLemmas)
  {
    // Also must preprocess the new lemmas. This is especially important for
    // formulas containing witness terms whose bodies are not in preprocessed
    // form, as term formula removal introduces new lemmas for these that
    // require theory-preprocessing.
    size_t i = 0;
    while (i < newLemmas.size())
    {
      TrustNode cur = newLemmas[i];
      newLemmas[i] = preprocessLemmaInternal(cur, newLemmas, newSkolems, false);
      i++;
    }
  }
  return tret;
}

TrustNode TheoryPreprocessor::preprocessLemma(TrustNode node,
                                              std::vector<TrustNode>& newLemmas,
                                              std::vector<Node>& newSkolems)
{
  return preprocessLemmaInternal(node, newLemmas, newSkolems, true);
}

TrustNode TheoryPreprocessor::preprocessLemmaInternal(
    TrustNode node,
    std::vector<TrustNode>& newLemmas,
    std::vector<Node>& newSkolems,
    bool procLemmas)
{
  // what was originally proven
  Node lemma = node.getProven();
  TrustNode tplemma =
      preprocessInternal(lemma, newLemmas, newSkolems, procLemmas);
  if (tplemma.isNull())
  {
    // no change needed
    return node;
  }
  Assert(tplemma.getKind() == TrustNodeKind::REWRITE);
  // what it was preprocessed to
  Node lemmap = tplemma.getNode();
  Assert(lemmap != node.getProven());
  // process the preprocessing
  if (isProofEnabled())
  {
    Assert(d_lp != nullptr);
    // add the original proof to the lazy proof
    d_lp->addLazyStep(node.getProven(), node.getGenerator());
    // only need to do anything if lemmap changed in a non-trivial way
    if (!CDProof::isSame(lemmap, lemma))
    {
      d_lp->addLazyStep(tplemma.getProven(),
                        tplemma.getGenerator(),
                        PfRule::PREPROCESS_LEMMA,
                        true,
                        "TheoryEngine::lemma_pp");
      // ---------- from node -------------- from theory preprocess
      // lemma                lemma = lemmap
      // ------------------------------------------ EQ_RESOLVE
      // lemmap
      std::vector<Node> pfChildren;
      pfChildren.push_back(lemma);
      pfChildren.push_back(tplemma.getProven());
      d_lp->addStep(lemmap, PfRule::EQ_RESOLVE, pfChildren, {});
    }
  }
  return TrustNode::mkTrustLemma(lemmap, d_lp.get());
}

RemoveTermFormulas& TheoryPreprocessor::getRemoveTermFormulas()
{
  return d_tfr;
}

struct preprocess_stack_element
{
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode n) : node(n), children_added(false) {}
};

TrustNode TheoryPreprocessor::theoryPreprocess(TNode assertion,
                                    std::vector<TrustNode>& newLemmas,
                                    std::vector<Node>& newSkolems)
{
  Trace("theory::preprocess")
      << "TheoryPreprocessor::theoryPreprocess(" << assertion << ")" << endl;
  // spendResource();

  // Do a topological sort of the subexpressions and substitute them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    preprocess_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    Trace("theory::preprocess-debug")
        << "TheoryPreprocessor::theoryPreprocess processing " << current << endl;

    // If node already in the cache we're done, pop from the stack
    NodeMap::iterator find = d_rtfCache.find(current);
    if (find != d_rtfCache.end())
    {
      toVisit.pop_back();
      continue;
    }

    if (!d_logicInfo.isTheoryEnabled(Theory::theoryOf(current))
        && Theory::theoryOf(current) != THEORY_SAT_SOLVER)
    {
      stringstream ss;
      ss << "The logic was specified as " << d_logicInfo.getLogicString()
         << ", which doesn't include " << Theory::theoryOf(current)
         << ", but got a preprocessing-time fact for that theory." << endl
         << "The fact:" << endl
         << current;
      throw LogicException(ss.str());
    }
    
    Trace("ajr-temp") << "Theoryof(" << current << ")=" << Theory::theoryOf(current)  << std::endl;

    // If this is an atom, we preprocess its terms with the theory ppRewriter
    if (Theory::theoryOf(current) != THEORY_BOOL)
    {
      Trace("ajr-temp") << "PP atom: " << current << std::endl;
      Node ppRewritten = ppTheoryRewrite(current);
      Trace("ajr-temp") << "PP pp: " << ppRewritten << std::endl;
      Assert(Rewriter::rewrite(ppRewritten)== ppRewritten);
      if (isProofEnabled() && ppRewritten!=current)
      {
        TrustNode trn = TrustNode::mkTrustRewrite(current, ppRewritten, d_tpg.get());
        registerTrustedRewrite(trn, d_tpgRtf.get(), true);
      }
      
      // term formula removal without fixed point, followed by rewrite here
      TrustNode ttfr = d_tfr.run(ppRewritten, newLemmas, newSkolems, false);
      Node rtfNode = ppRewritten;
      if (!ttfr.isNull())
      {
        rtfNode = ttfr.getNode();
        Trace("ajr-temp") << "PP rtf: " << rtfNode << std::endl;
        registerTrustedRewrite(ttfr, d_tpgRtf.get(), true);
      }
      d_rtfCache[current] = rtfNode;
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.children_added)
    {
      // Children have been processed, so substitute
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(d_rtfCache.find(current[i]) != d_rtfCache.end());
        builder << d_rtfCache[current[i]].get();
      }
      // Mark the substitution and continue
      Node result = builder;
      Trace("theory::preprocess-debug")
          << "TheoryPreprocessor::theoryPreprocess setting " << current << " -> " << result << endl;
      d_rtfCache[current] = result;
      toVisit.pop_back();
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0)
      {
        stackHead.children_added = true;
        // We need to add the children
        for (TNode::iterator child_it = current.begin();
             child_it != current.end();
             ++child_it)
        {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = d_rtfCache.find(childNode);
          if (childFind == d_rtfCache.end())
          {
            toVisit.push_back(childNode);
          }
        }
      }
      else
      {
        // No children, so we're done
        Trace("theory::preprocess-debug")
            << "SubstitutionMap::internalSubstitute setting " << current << " -> " << current << endl;
        d_rtfCache[current] = current;
        toVisit.pop_back();
      }
    }
  }
  Assert (d_rtfCache.find(assertion)!=d_rtfCache.end());
  // Return the substituted version
  Node res = d_rtfCache[assertion];
  return TrustNode::mkTrustRewrite(assertion, res, d_tpg.get());
}

// Recursively traverse a term and call the theory rewriter on its sub-terms
Node TheoryPreprocessor::ppTheoryRewrite(TNode term)
{
  NodeMap::iterator find = d_ppCache.find(term);
  if (find != d_ppCache.end())
  {
    return (*find).second;
  }
  if (term.getNumChildren() == 0)
  {
    return preprocessWithProof(term);
  }
  // should be in rewritten form here
  Assert(term == Rewriter::rewrite(term));
  Trace("theory-pp") << "ppTheoryRewrite { " << term << endl;
  // do not rewrite inside quantifiers
  Node newTerm = term;
  if (!term.isClosure())
  {
    NodeBuilder<> newNode(term.getKind());
    if (term.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      newNode << term.getOperator();
    }
    for (const Node& nt : term)
    {
      newNode << ppTheoryRewrite(nt);
    }
    newTerm = Node(newNode);
    newTerm = rewriteWithProof(newTerm, d_tpg.get(), false);
  }
  newTerm = preprocessWithProof(newTerm);
  d_ppCache[term] = newTerm;
  Trace("theory-pp") << "ppTheoryRewrite returning " << newTerm << "}" << endl;
  return newTerm;
}

Node TheoryPreprocessor::rewriteWithProof(Node term, TConvProofGenerator* pg, bool isPre)
{
  Node termr = Rewriter::rewrite(term);
  // store rewrite step if tracking proofs and it rewrites
  if (isProofEnabled())
  {
    // may rewrite the same term more than once, thus check hasRewriteStep
    if (termr != term)
    {
      Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (rewriting) "
                         << term << " -> " << termr << std::endl;
      // always use term context hash 0 (default)
      pg->addRewriteStep(term, termr, PfRule::REWRITE, {}, {term}, isPre);
    }
  }
  return termr;
}

Node TheoryPreprocessor::preprocessWithProof(Node term)
{
  // Important that it is in rewritten form, to ensure that the rewrite steps
  // recorded in d_tpg are functional. In other words, there should not
  // be steps from the same term to multiple rewritten forms, which would be
  // the case if we registered a preprocessing step for a non-rewritten term.
  Assert(term == Rewriter::rewrite(term));
  // We never call ppRewrite on equalities here, since equalities have a
  // special status. In particular, notice that theory preprocessing can be
  // called on all formulas asserted to theory engine, including those generated
  // as new literals appearing in lemmas. Calling ppRewrite on equalities is
  // incompatible with theory combination where a split on equality requested
  // by a theory could be preprocessed to something else, thus making theory
  // combination either non-terminating or result in solution soundness.
  // Notice that an alternative solution is to ensure that certain lemmas
  // (e.g. splits from theory combination) can never have theory preprocessing
  // applied to them. However, it is more uniform to say that theory
  // preprocessing is applied to all formulas. This makes it so that e.g.
  // theory solvers do not need to specify whether they want their lemmas to
  // be theory-preprocessed or not.
  if (term.getKind() == kind::EQUAL)
  {
    return term;
  }
  // call ppRewrite for the given theory
  TrustNode trn = d_engine.theoryOf(term)->ppRewrite(term);
  if (trn.isNull())
  {
    // no change, return original term
    return term;
  }
  Node termr = trn.getNode();
  Assert(term != termr);
  if (isProofEnabled())
  {
    registerTrustedRewrite(trn, d_tpg.get(), false);
  }
  termr = rewriteWithProof(termr, d_tpg.get(), true);
  return ppTheoryRewrite(termr);
}

bool TheoryPreprocessor::isProofEnabled() const { return d_tpg != nullptr; }

void TheoryPreprocessor::registerTrustedRewrite(TrustNode trn, TConvProofGenerator* pg, bool isPre)
{
  if (!isProofEnabled() || trn.isNull())
  {
    return;
  }
  Assert (trn.getKind()==TrustNodeKind::REWRITE);
  Node eq = trn.getProven();
  Node term = eq[0];
  Node termr = eq[1];
  if (trn.getGenerator() != nullptr)
  {
    Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (generator) "
                        << term << " -> " << termr << std::endl;
    trn.debugCheckClosed("tpp-debug",
                          "TheoryPreprocessor::preprocessWithProof");
    // always use term context hash 0 (default)
    pg->addRewriteStep(
        term, termr, trn.getGenerator(), isPre, PfRule::ASSUME, true);
  }
  else
  {
    Trace("tpp-debug") << "TheoryPreprocessor: addRewriteStep (trusted) "
                        << term << " -> " << termr << std::endl;
    // small step trust
    pg->addRewriteStep(term,
                          termr,
                          PfRule::THEORY_PREPROCESS,
                          {},
                          {term.eqNode(termr)},
                          isPre);
  }
}

}  // namespace theory
}  // namespace CVC4
