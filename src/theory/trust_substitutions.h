/*********************                                                        */
/*! \file trust_substitutions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Trust substitutions
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__TRUST_SUBSTITUTIONS_H
#define CVC4__THEORY__TRUST_SUBSTITUTIONS_H

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/lazy_proof.h"
#include "expr/proof_node_manager.h"
#include "expr/term_conversion_proof_generator.h"
#include "theory/eager_proof_generator.h"
#include "theory/substitutions.h"
#include "theory/theory_proof_step_buffer.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace theory {

/**
 * A layer on top of SubstitutionMap that tracks proofs.
 */
class TrustSubstitutionMap
{
 public:
  TrustSubstitutionMap(context::Context* c,
                       ProofNodeManager* pnm,
                       std::string name = "TrustSubstitutionMap",
                       PfRule trustId = PfRule::TRUST,
                       MethodId ids = MethodId::SB_DEFAULT);
  /** Gets a reference to the underlying substitution map */
  SubstitutionMap& get();
  /**
   * Add substitution x -> t, where pg can provide a closed proof of (= x t)
   * in the remainder of this user context.
   */
  void addSubstitution(TNode x, TNode t, ProofGenerator* pg = nullptr);
  /**
   * Add substitution x -> t from a single step.
   */
  void addSubstitution(TNode x, TNode t, PfRule id, std::vector<Node>& args);
  /**
   * Add substitution x -> t, which was derived from the proven field of
   * trust node tn. In other words, (= x t) is the solved form of
   * tn.getProven(). This method is a helper function for methods (e.g.
   * ppAssert) that put literals into solved form. It should be the case
   * that (= x t) and tn.getProven() can be shown equivalent by rewriting.
   *
   * This ensures that we add a substitution with a proof
   * based on transforming the tn.getProven() to (= x t) if tn has a
   * non-null proof generator; otherwise if tn has no proof generator
   * we simply add the substitution.
   */
  void addSubstitutionSolved(TNode x, TNode t, TrustNode tn);
  /**
   * Add substitutions
   */
  void addSubstitutions(TrustSubstitutionMap& t);
  /**
   * Apply substitutions in this class to node n. Returns a trust node
   * proving n = n*sigma, where the proof generator is provided by this class
   * (when proofs are enabled).
   */
  TrustNode apply(Node n, bool doRewrite = true);

 private:
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /**
   * Get current substitution. This returns a node of the form:
   *   (and (= x1 t1) ... (= xn tn))
   * where (x1, t1) ... (xn, tn) have been registered via addSubstitution above.
   * Moreover, it ensures that d_subsPg has a proof of the returned value.
   */
  Node getCurrentSubstitution();
  /**
   * Allocate a helper proof. This returns a fresh lazy proof object that
   * remains alive in the context given by this class. This feature is used to
   * construct helper proofs, e.g. to support the skeleton of proofs that
   * connect solving steps in addSubstitutionSolved.
   */
  LazyCDProof* allocateHelperProof();
  /** The substitution map */
  SubstitutionMap d_subs;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** A context-dependent list of trust nodes */
  context::CDList<TrustNode> d_tsubs;
  /** Theory proof step buffer */
  std::unique_ptr<TheoryProofStepBuffer> d_tspb;
  /** A lazy proof for substitution steps */
  std::unique_ptr<LazyCDProof> d_subsPg;
  /** A lazy proof for apply steps */
  std::unique_ptr<LazyCDProof> d_applyPg;
  /** A context-dependent list of LazyCDProof, allocated for solve steps */
  context::CDList<std::shared_ptr<LazyCDProof> > d_solveProofs;
  /** Whether the substitution is up-to-date */
  context::CDO<Node> d_currentSubs;
  /** Name for debugging */
  std::string d_name;
  /**
   * The placeholder trusted PfRule identifier for calls to addSubstitution
   * that are not given proof generators.
   */
  PfRule d_trustId;
  /** The method id for which form of substitution to apply */
  MethodId d_ids;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__TRUST_SUBSTITUTIONS_H */
