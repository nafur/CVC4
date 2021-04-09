/*********************                                                        */
/*! \file expr_miner_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Expression miner manager, which manages individual expression miners.
 **/

#include "cvc4_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EXPR_MINER_MANAGER_H
#define CVC5__THEORY__QUANTIFIERS__EXPR_MINER_MANAGER_H

#include "expr/node.h"
#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/quantifiers/query_generator.h"
#include "theory/quantifiers/solution_filter.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/** ExpressionMinerManager
 *
 * This class manages a set of expression miners. It provides a common place
 * to register expressions so that multiple mining algorithms can be run in
 * coordination, possibly sharing information and utilities like a common
 * sampling object.
 */
class ExpressionMinerManager
{
 public:
  ExpressionMinerManager();
  ~ExpressionMinerManager() {}
  /**  Initialize this class
   *
   * Initializes this class, informing it that the free variables of terms
   * added to this class via addTerm will have free variables that are a subset
   * of vars, and have type tn. All expression miners in this class with be
   * initialized with this variable list. The arguments nsamples and
   * unique_type_ids are used for initializing the sampler class of this manager
   * (see SygusSampler::initialize for details).
   */
  void initialize(const std::vector<Node>& vars,
                  TypeNode tn,
                  unsigned nsamples,
                  bool unique_type_ids = false);
  /** Initialize this class, sygus version
   *
   * Initializes this class, informing it that the terms added to this class
   * via calls to addTerm will be generated by the grammar of f. The method
   * takes a pointer to the quantifiers engine qe. If the argument useSygusType
   * is true, the terms added to this class are the sygus datatype terms.
   * If useSygusType is false, the terms are the builtin equivalent of these
   * terms. The argument nsamples is used to initialize the sampler.
   */
  void initializeSygus(TermDbSygus* tds,
                       Node f,
                       unsigned nsamples,
                       bool useSygusType);
  /** enable rewrite rule synthesis (--sygus-rr-synth) */
  void enableRewriteRuleSynth();
  /** enable query generation (--sygus-query-gen) */
  void enableQueryGeneration(unsigned deqThresh);
  /** filter strong solutions (--sygus-filter-sol=strong) */
  void enableFilterStrongSolutions();
  /** filter weak solutions (--sygus-filter-sol=weak) */
  void enableFilterWeakSolutions();
  /** add term
   *
   * Expression miners may print information on the output stream out, for
   * instance, candidate-rewrites. The method returns true if the term sol is
   * distinct (up to T-equivalence) with all previous terms added to this class,
   * which is computed based on the miners that this manager enables.
   */
  bool addTerm(Node sol, std::ostream& out);
  /**
   * Same as above, but the argument rew_print is set to true if a rewrite rule
   * was printed on the output stream out.
   */
  bool addTerm(Node sol, std::ostream& out, bool& rew_print);

 private:
  /** whether we are doing rewrite synthesis */
  bool d_doRewSynth;
  /** whether we are doing query generation */
  bool d_doQueryGen;
  /** whether we are filtering solutions based on logical strength */
  bool d_doFilterLogicalStrength;
  /** the sygus function passed to initializeSygus, if any */
  Node d_sygus_fun;
  /** whether we are using sygus types */
  bool d_use_sygus_type;
  /** the sygus term database of the quantifiers engine */
  TermDbSygus* d_tds;
  /** candidate rewrite database */
  CandidateRewriteDatabase d_crd;
  /** query generator */
  QueryGenerator d_qg;
  /** solution filter based on logical strength */
  SolutionFilterStrength d_sols;
  /** sygus sampler object */
  SygusSampler d_sampler;
  /** extended rewriter object */
  ExtendedRewriter d_ext_rew;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__EXPR_MINER_MANAGER_H */
