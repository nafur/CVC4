/*********************                                                        */
/*! \file quantifiers_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory instantiator, Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS_ENGINE_H
#define CVC4__THEORY__QUANTIFIERS_ENGINE_H

#include <map>
#include <unordered_map>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "theory/quantifiers/quant_util.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

class DecisionManager;
class QuantifiersModule;
class RepSetIterator;

namespace inst {
class TriggerTrie;
}
namespace quantifiers {
class FirstOrderModel;
class Instantiate;
class QModelBuilder;
class QuantifiersInferenceManager;
class QuantifiersModules;
class QuantifiersState;
class QuantifiersRegistry;
class Skolemize;
class TermDb;
class TermDbSygus;
class TermEnumeration;
class TermRegistry;
}

// TODO: organize this more/review this, github issue #1163
class QuantifiersEngine {
  friend class ::CVC4::TheoryEngine;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  typedef context::CDList<Node> NodeList;
  typedef context::CDList<bool> BoolList;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  QuantifiersEngine(quantifiers::QuantifiersState& qstate,
                    quantifiers::QuantifiersRegistry& qr,
                    quantifiers::TermRegistry& tr,
                    quantifiers::QuantifiersInferenceManager& qim,
                    quantifiers::FirstOrderModel* qm,
                    ProofNodeManager* pnm);
  ~QuantifiersEngine();
  //---------------------- external interface
  /** Get the decision manager */
  DecisionManager* getDecisionManager();
  /** The quantifiers state object */
  quantifiers::QuantifiersState& getState();
  /** The quantifiers inference manager */
  quantifiers::QuantifiersInferenceManager& getInferenceManager();
  /** The quantifiers registry */
  quantifiers::QuantifiersRegistry& getQuantifiersRegistry();
  //---------------------- end external interface
  //---------------------- utilities
  /** get the model builder */
  quantifiers::QModelBuilder* getModelBuilder() const;
  /** get model */
  quantifiers::FirstOrderModel* getModel() const;
  /** get term database */
  quantifiers::TermDb* getTermDatabase() const;
  /** get term database sygus */
  quantifiers::TermDbSygus* getTermDatabaseSygus() const;
  /** get term enumeration utility */
  quantifiers::TermEnumeration* getTermEnumeration() const;
  /** get instantiate utility */
  quantifiers::Instantiate* getInstantiate() const;
  /** get skolemize utility */
  quantifiers::Skolemize* getSkolemize() const;
  /** get trigger database */
  inst::TriggerTrie* getTriggerDatabase() const;
  //---------------------- end utilities
 private:
  //---------------------- private initialization
  /**
   * Finish initialize, which passes pointers to the objects that quantifiers
   * engine needs but were not available when it was created. This is
   * called after theories have been created but before they have finished
   * initialization.
   *
   * @param te The theory engine
   * @param dm The decision manager of the theory engine
   */
  void finishInit(TheoryEngine* te, DecisionManager* dm);
  //---------------------- end private initialization

 public:
  /** presolve */
  void presolve();
  /** notify preprocessed assertion */
  void ppNotifyAssertions(const std::vector<Node>& assertions);
  /** check at level */
  void check( Theory::Effort e );
  /** notify that theories were combined */
  void notifyCombineTheories();
  /** preRegister quantifier
   *
   * This function is called after registerQuantifier for quantified formulas
   * that are pre-registered to the quantifiers theory.
   */
  void preRegisterQuantifier(Node q);
  /** assert universal quantifier */
  void assertQuantifier( Node q, bool pol );
private:
 /** (context-indepentent) register quantifier internal
  *
  * This is called when a quantified formula q is pre-registered to the
  * quantifiers theory, and updates the modules in this class with
  * context-independent information about how to handle q. This includes basic
  * information such as which module owns q.
  */
 void registerQuantifierInternal(Node q);
 /** reduceQuantifier, return true if reduced */
 bool reduceQuantifier(Node q);

public:
 /** notification when master equality engine is updated */
 void eqNotifyNewClass(TNode t);
 /** mark relevant quantified formula, this will indicate it should be checked
  * before the others */
 void markRelevant(Node q);
 /**
  * Get quantifiers name, which returns a variable corresponding to the name of
  * quantified formula q if q has a name, or otherwise returns q itself.
  */
 Node getNameForQuant(Node q) const;
 /**
  * Get name for quantified formula. Returns true if q has a name or if req
  * is false. Sets name to the result of the above method.
  */
 bool getNameForQuant(Node q, Node& name, bool req = true) const;

public:
 //----------user interface for instantiations (see quantifiers/instantiate.h)
 /** print solution for synthesis conjectures */
 void printSynthSolution(std::ostream& out);
 /** get list of quantified formulas that were instantiated */
 void getInstantiatedQuantifiedFormulas(std::vector<Node>& qs);
 /** get instantiation term vectors */
 void getInstantiationTermVectors(Node q,
                                  std::vector<std::vector<Node> >& tvecs);
 void getInstantiationTermVectors(
     std::map<Node, std::vector<std::vector<Node> > >& insts);
 /**
  * Get skolemization vectors, where for each quantified formula that was
  * skolemized, this is the list of skolems that were used to witness the
  * negation of that quantified formula.
  */
 void getSkolemTermVectors(std::map<Node, std::vector<Node> >& sks) const;

 /** get synth solutions
  *
  * This method returns true if there is a synthesis solution available. This
  * is the case if the last call to check satisfiability originated in a
  * check-synth call, and the synthesis engine module of this class
  * successfully found a solution for all active synthesis conjectures.
  *
  * This method adds entries to sol_map that map functions-to-synthesize with
  * their solutions, for all active conjectures. This should be called
  * immediately after the solver answers unsat for sygus input.
  *
  * For details on what is added to sol_map, see
  * SynthConjecture::getSynthSolutions.
  */
 bool getSynthSolutions(std::map<Node, std::map<Node, Node> >& sol_map);

 //----------end user interface for instantiations

 /** statistics class */
 class Statistics
 {
  public:
    TimerStat d_time;
    TimerStat d_qcf_time;
    TimerStat d_ematching_time;
    IntStat d_num_quant;
    IntStat d_instantiation_rounds;
    IntStat d_instantiation_rounds_lc;
    IntStat d_triggers;
    IntStat d_simple_triggers;
    IntStat d_multi_triggers;
    IntStat d_red_alpha_equiv;
    Statistics();
    ~Statistics();
  };/* class QuantifiersEngine::Statistics */
  Statistics d_statistics;

 private:
  /** The quantifiers state object */
  quantifiers::QuantifiersState& d_qstate;
  /** The quantifiers inference manager */
  quantifiers::QuantifiersInferenceManager& d_qim;
  /** Pointer to theory engine object */
  TheoryEngine* d_te;
  /** Reference to the decision manager of the theory engine */
  DecisionManager* d_decManager;
  /** Pointer to the proof node manager */
  ProofNodeManager* d_pnm;
  /** vector of utilities for quantifiers */
  std::vector<QuantifiersUtil*> d_util;
  /** vector of modules for quantifiers */
  std::vector<QuantifiersModule*> d_modules;
  //------------- quantifiers utilities
  /** The quantifiers registry */
  quantifiers::QuantifiersRegistry& d_qreg;
  /** The term registry */
  quantifiers::TermRegistry& d_treg;
  /** all triggers will be stored in this trie */
  std::unique_ptr<inst::TriggerTrie> d_tr_trie;
  /** extended model object */
  quantifiers::FirstOrderModel* d_model;
  //------------- end quantifiers utilities
  /**
   * The modules utility, which contains all of the quantifiers modules.
   */
  std::unique_ptr<quantifiers::QuantifiersModules> d_qmodules;
  //------------- end temporary information during check
 private:
  /** list of all quantifiers seen */
  std::map<Node, bool> d_quants;
  /** quantifiers pre-registered */
  NodeSet d_quants_prereg;
  /** quantifiers reduced */
  BoolMap d_quants_red;
  std::map<Node, Node> d_quants_red_lem;
};/* class QuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS_ENGINE_H */
