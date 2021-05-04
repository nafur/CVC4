/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of setting default options.
 */

#include "smt/set_defaults.h"

#include <sstream>

#include "base/output.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/open_ostream.h"
#include "options/option_exception.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/prop_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/set_language.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "smt/logic_exception.h"
#include "theory/theory.h"

using namespace cvc5::theory;

namespace cvc5 {
namespace smt {

void setDefaults(LogicInfo& logic, bool isInternalSubsolver)
{
  Options& opts = Options::current();
  // implied options
  if (options::debugCheckModels())
  {
    opts.set(options::checkModels, true);
  }
  if (options::checkModels() || options::dumpModels())
  {
    opts.set(options::produceModels, true);
  }
  if (options::checkModels())
  {
    opts.set(options::produceAssignments, true);
  }
  // unsat cores and proofs shenanigans
  if (options::dumpUnsatCoresFull())
  {
    opts.set(options::dumpUnsatCores, true);
  }
  if (options::checkUnsatCores() || options::dumpUnsatCores()
      || options::unsatAssumptions()
      || options::unsatCoresMode() != options::UnsatCoresMode::OFF)
  {
    opts.set(options::unsatCores, true);
  }
  if (options::unsatCores()
      && options::unsatCoresMode() == options::UnsatCoresMode::OFF)
  {
    if (opts.smt->unsatCoresMode__setByUser__)
    {
      Notice()
          << "Overriding OFF unsat-core mode since cores were requested..\n";
    }
    opts.set(options::unsatCoresMode, options::UnsatCoresMode::OLD_PROOF);
  }

  if (options::checkProofs() || options::dumpProofs())
  {
    opts.set(options::produceProofs, true);
  }

  if (options::produceProofs()
      && options::unsatCoresMode() != options::UnsatCoresMode::FULL_PROOF)
  {
    if (opts.smt->unsatCoresMode__setByUser__)
    {
      Notice() << "Forcing full-proof mode for unsat cores mode since proofs "
                  "were requested.\n";
    }
    // enable unsat cores, because they are available as a consequence of proofs
    opts.set(options::unsatCores, true);
    opts.set(options::unsatCoresMode, options::UnsatCoresMode::FULL_PROOF);
  }

  // set proofs on if not yet set
  if (options::unsatCores() && !options::produceProofs()
      && options::unsatCoresMode() != options::UnsatCoresMode::OLD_PROOF)
  {
    if (opts.smt->produceProofs__setByUser__)
    {
      Notice()
          << "Forcing proof production since new unsat cores were requested.\n";
    }
    opts.set(options::produceProofs, true);
  }

  // if unsat cores are disabled, then unsat cores mode should be OFF
  Assert(options::unsatCores()
         == (options::unsatCoresMode() != options::UnsatCoresMode::OFF));

  if (opts.bv->bitvectorAigSimplifications__setByUser__)
  {
    Notice() << "SmtEngine: setting bitvectorAig" << std::endl;
    opts.set(options::bitvectorAig, true);
  }
  if (opts.bv->bitvectorAlgebraicBudget__setByUser__)
  {
    Notice() << "SmtEngine: setting bitvectorAlgebraicSolver" << std::endl;
    opts.set(options::bitvectorAlgebraicSolver, true);
  }

  bool isSygus = language::isInputLangSygus(options::inputLanguage());
  bool usesSygus = isSygus;

  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    if (options::produceModels()
        && (logic.isTheoryEnabled(THEORY_ARRAYS)
            || logic.isTheoryEnabled(THEORY_UF)))
    {
      if (opts.bv->bitblastMode__setByUser__
          || opts.smt->produceModels__setByUser__)
      {
        throw OptionException(std::string(
            "Eager bit-blasting currently does not support model generation "
            "for the combination of bit-vectors with arrays or uinterpreted "
            "functions. Try --bitblast=lazy"));
      }
      Notice() << "SmtEngine: setting bit-blast mode to lazy to support model"
               << "generation" << std::endl;
      opts.set(options::bitblastMode, options::BitblastMode::LAZY);
    }
    else if (!options::incrementalSolving())
    {
      opts.set(options::ackermann, true);
    }

    if (options::incrementalSolving() && !logic.isPure(THEORY_BV))
    {
      throw OptionException(
          "Incremental eager bit-blasting is currently "
          "only supported for QF_BV. Try --bitblast=lazy.");
    }

    // Force lazy solver since we don't handle EAGER_ATOMS in the
    // BVSolver::BITBLAST solver.
    opts.set(options::bvSolver, options::BVSolver::LAZY);
  }

  /* Only BVSolver::LAZY natively supports int2bv and nat2bv, for other solvers
   * we need to eagerly eliminate the operators. */
  if (options::bvSolver() == options::BVSolver::SIMPLE
      || options::bvSolver() == options::BVSolver::BITBLAST)
  {
    opts.set(options::bvLazyReduceExtf, false);
    opts.set(options::bvLazyRewriteExtf, false);
  }

  /* Disable bit-level propagation by default for the BITBLAST solver. */
  if (options::bvSolver() == options::BVSolver::BITBLAST)
  {
    opts.set(options::bitvectorPropagate, false);
  }

  if (options::solveIntAsBV() > 0)
  {
    // not compatible with incremental
    if (options::incrementalSolving())
    {
      throw OptionException(
          "solving integers as bitvectors is currently not supported "
          "when solving incrementally.");
    }
    // Int to BV currently always eliminates arithmetic completely (or otherwise
    // fails). Thus, it is safe to eliminate arithmetic. Also, bit-vectors
    // are required.
    logic = logic.getUnlockedCopy();
    logic.enableTheory(THEORY_BV);
    logic.disableTheory(THEORY_ARITH);
    logic.lock();
  }

  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      throw OptionException(
          "solving bitvectors as integers is incompatible with --bool-to-bv.");
    }
    if (options::BVAndIntegerGranularity() > 8)
    {
      /**
       * The granularity sets the size of the ITE in each element
       * of the sum that is generated for bitwise operators.
       * The size of the ITE is 2^{2*granularity}.
       * Since we don't want to introduce ITEs with unbounded size,
       * we bound the granularity.
       */
      throw OptionException("solve-bv-as-int accepts values from 0 to 8.");
    }
    if (logic.isTheoryEnabled(THEORY_BV))
    {
      logic = logic.getUnlockedCopy();
      logic.enableTheory(THEORY_ARITH);
      logic.arithNonLinear();
      logic.lock();
    }
  }

  // set options about ackermannization
  if (options::ackermann() && options::produceModels()
      && (logic.isTheoryEnabled(THEORY_ARRAYS)
          || logic.isTheoryEnabled(THEORY_UF)))
  {
    if (opts.smt->produceModels__setByUser__)
    {
      throw OptionException(std::string(
          "Ackermannization currently does not support model generation."));
    }
    Notice() << "SmtEngine: turn off ackermannization to support model"
             << "generation" << std::endl;
    opts.set(options::ackermann, false);
  }

  if (options::ackermann())
  {
    if (options::incrementalSolving())
    {
      throw OptionException(
          "Incremental Ackermannization is currently not supported.");
    }

    if (logic.isQuantified())
    {
      throw LogicException("Cannot use Ackermannization on quantified formula");
    }

    if (logic.isTheoryEnabled(THEORY_UF))
    {
      logic = logic.getUnlockedCopy();
      logic.disableTheory(THEORY_UF);
      logic.lock();
    }
    if (logic.isTheoryEnabled(THEORY_ARRAYS))
    {
      logic = logic.getUnlockedCopy();
      logic.disableTheory(THEORY_ARRAYS);
      logic.lock();
    }
  }

  // --ite-simp is an experimental option designed for QF_LIA/nec. This
  // technique is experimental. This benchmark set also requires removing ITEs
  // during preprocessing, before repeating simplification. Hence, we enable
  // this by default.
  if (options::doITESimp())
  {
    if (!opts.smt->earlyIteRemoval__setByUser__)
    {
      opts.set(options::earlyIteRemoval, true);
    }
  }

  // Set default options associated with strings-exp. We also set these options
  // if we are using eager string preprocessing, which may introduce quantified
  // formulas at preprocess time.
  if (!logic.hasEverything() && logic.isTheoryEnabled(THEORY_STRINGS))
  {
    // If the user explicitly set a logic that includes strings, but is not
    // the generic "ALL" logic, then enable stringsExp.
    opts.set(options::stringExp, true);
  }
  if (options::stringExp() || !options::stringLazyPreproc())
  {
    // We require quantifiers since extended functions reduce using them.
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
      Trace("smt") << "turning on quantifier logic, for strings-exp"
                   << std::endl;
    }
    // We require bounded quantifier handling.
    if (!opts.quantifiers->fmfBound__setByUser__)
    {
      opts.set(options::fmfBound, true);
      Trace("smt") << "turning on fmf-bound-int, for strings-exp" << std::endl;
    }
    // Note we allow E-matching by default to support combinations of sequences
    // and quantifiers.
  }
  // whether we must disable proofs
  bool disableProofs = false;
  if (options::globalNegate())
  {
    // When global negate answers "unsat", it is not due to showing a set of
    // formulas is unsat. Thus, proofs do not apply.
    disableProofs = true;
  }

  // new unsat core specific restrictions for proofs
  if (options::unsatCores()
      && options::unsatCoresMode() != options::UnsatCoresMode::OLD_PROOF
      && options::unsatCoresMode() != options::UnsatCoresMode::FULL_PROOF)
  {
    // no fine-graininess
    if (!opts.proof->proofGranularityMode__setByUser__)
    {
      opts.set(options::proofGranularityMode, options::ProofGranularityMode::OFF);
    }
  }

  if (options::arraysExp())
  {
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
    }
    // Allows to answer sat more often by default.
    if (!opts.quantifiers->fmfBound__setByUser__)
    {
      opts.set(options::fmfBound, true);
      Trace("smt") << "turning on fmf-bound, for arrays-exp" << std::endl;
    }
  }

  // sygus inference may require datatypes
  if (!isInternalSubsolver)
  {
    if (options::produceAbducts()
        || options::produceInterpols() != options::ProduceInterpols::NONE
        || options::sygusInference() || options::sygusRewSynthInput())
    {
      // since we are trying to recast as sygus, we assume the input is sygus
      isSygus = true;
      usesSygus = true;
    }
    else if (options::sygusInst())
    {
      // sygus instantiation uses sygus, but it is not a sygus problem
      usesSygus = true;
    }
  }

  // We now know whether the input uses sygus. Update the logic to incorporate
  // the theories we need internally for handling sygus problems.
  if (usesSygus)
  {
    logic = logic.getUnlockedCopy();
    logic.enableSygus();
    logic.lock();
    if (isSygus)
    {
      // When sygus answers "unsat", it is not due to showing a set of
      // formulas is unsat in the standard way. Thus, proofs do not apply.
      disableProofs = true;
    }
  }

  // if we requiring disabling proofs, disable them now
  if (disableProofs && options::produceProofs())
  {
    opts.set(options::unsatCores, false);
    opts.set(options::unsatCoresMode, options::UnsatCoresMode::OFF);
    if (options::produceProofs())
    {
      Notice() << "SmtEngine: turning off produce-proofs." << std::endl;
    }
    opts.set(options::produceProofs, false);
    opts.set(options::checkProofs, false);
    opts.set(options::proofEagerChecking, false);
  }

  // sygus core connective requires unsat cores
  if (options::sygusCoreConnective())
  {
    opts.set(options::unsatCores, true);
    if (options::unsatCoresMode() == options::UnsatCoresMode::OFF)
    {
      opts.set(options::unsatCoresMode, options::UnsatCoresMode::OLD_PROOF);
    }
  }

  if ((options::checkModels() || options::checkSynthSol()
       || options::produceAbducts()
       || options::produceInterpols() != options::ProduceInterpols::NONE
       || options::modelCoresMode() != options::ModelCoresMode::NONE
       || options::blockModelsMode() != options::BlockModelsMode::NONE
       || options::produceProofs())
      && !options::produceAssertions())
  {
    Notice() << "SmtEngine: turning on produce-assertions to support "
             << "option requiring assertions." << std::endl;
    opts.set(options::produceAssertions, true);
  }

  // whether we want to force safe unsat cores, i.e., if we are in the OLD_PROOF
  // unsat core mode, since new ones are experimental
  bool safeUnsatCores =
      options::unsatCoresMode() == options::UnsatCoresMode::OLD_PROOF;

  // Disable options incompatible with incremental solving, unsat cores or
  // output an error if enabled explicitly. It is also currently incompatible
  // with arithmetic, force the option off.
  if (options::incrementalSolving() || safeUnsatCores)
  {
    if (options::unconstrainedSimp())
    {
      if (opts.smt->unconstrainedSimp__setByUser__)
      {
        throw OptionException(
            "unconstrained simplification not supported with old unsat "
            "cores/incremental solving");
      }
      Notice() << "SmtEngine: turning off unconstrained simplification to "
                  "support old unsat cores/incremental solving"
               << std::endl;
      opts.set(options::unconstrainedSimp, false);
    }
  }
  else
  {
    // Turn on unconstrained simplification for QF_AUFBV
    if (!opts.smt->unconstrainedSimp__setByUser__)
    {
      bool uncSimp = !logic.isQuantified() && !options::produceModels()
                     && !options::produceAssignments()
                     && !options::checkModels()
                     && logic.isTheoryEnabled(THEORY_ARRAYS)
                     && logic.isTheoryEnabled(THEORY_BV)
                     && !logic.isTheoryEnabled(THEORY_ARITH);
      Trace("smt") << "setting unconstrained simplification to " << uncSimp
                   << std::endl;
      opts.set(options::unconstrainedSimp, uncSimp);
    }
  }

  if (options::incrementalSolving())
  {
    if (options::sygusInference())
    {
      if (opts.quantifiers->sygusInference__setByUser__)
      {
        throw OptionException(
            "sygus inference not supported with incremental solving");
      }
      Notice() << "SmtEngine: turning off sygus inference to support "
                  "incremental solving"
               << std::endl;
      opts.set(options::sygusInference, false);
    }
  }

  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    /**
     * Operations on 1 bits are better handled as Boolean operations
     * than as integer operations.
     * Therefore, we enable bv-to-bool, which runs before
     * the translation to integers.
     */
    opts.set(options::bitvectorToBool, true);
  }

  // Disable options incompatible with unsat cores or output an error if enabled
  // explicitly
  if (safeUnsatCores)
  {
    if (options::simplificationMode() != options::SimplificationMode::NONE)
    {
      if (opts.smt->simplificationMode__setByUser__)
      {
        throw OptionException(
            "simplification not supported with old unsat cores");
      }
      Notice() << "SmtEngine: turning off simplification to support unsat "
                  "cores"
               << std::endl;
      opts.set(options::simplificationMode, options::SimplificationMode::NONE);
    }

    if (options::pbRewrites())
    {
      if (opts.arith->pbRewrites__setByUser__)
      {
        throw OptionException(
            "pseudoboolean rewrites not supported with old unsat cores");
      }
      Notice() << "SmtEngine: turning off pseudoboolean rewrites to support "
                  "old unsat cores\n";
      opts.set(options::pbRewrites, false);
    }

    if (options::sortInference())
    {
      if (opts.smt->sortInference__setByUser__)
      {
        throw OptionException(
            "sort inference not supported with old unsat cores");
      }
      Notice() << "SmtEngine: turning off sort inference to support old unsat "
                  "cores\n";
      opts.set(options::sortInference, false);
    }

    if (options::preSkolemQuant())
    {
      if (opts.quantifiers->preSkolemQuant__setByUser__)
      {
        throw OptionException(
            "pre-skolemization not supported with old unsat cores");
      }
      Notice() << "SmtEngine: turning off pre-skolemization to support old "
                  "unsat cores\n";
      opts.set(options::preSkolemQuant, false);
    }

    if (options::bitvectorToBool())
    {
      if (opts.bv->bitvectorToBool__setByUser__)
      {
        throw OptionException("bv-to-bool not supported with old unsat cores");
      }
      Notice() << "SmtEngine: turning off bitvector-to-bool to support old "
                  "unsat cores\n";
      opts.set(options::bitvectorToBool, false);
    }

    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      if (opts.bv->boolToBitvector__setByUser__)
      {
        throw OptionException(
            "bool-to-bv != off not supported with old unsat cores");
      }
      Notice()
          << "SmtEngine: turning off bool-to-bv to support old unsat cores\n";
      opts.set(options::boolToBitvector, options::BoolToBVMode::OFF);
    }

    if (options::bvIntroducePow2())
    {
      if (opts.bv->bvIntroducePow2__setByUser__)
      {
        throw OptionException(
            "bv-intro-pow2 not supported with old unsat cores");
      }
      Notice()
          << "SmtEngine: turning off bv-intro-pow2 to support old unsat cores";
      opts.set(options::bvIntroducePow2, false);
    }

    if (options::repeatSimp())
    {
      if (opts.smt->repeatSimp__setByUser__)
      {
        throw OptionException("repeat-simp not supported with old unsat cores");
      }
      Notice()
          << "SmtEngine: turning off repeat-simp to support old unsat cores\n";
      opts.set(options::repeatSimp, false);
    }

    if (options::globalNegate())
    {
      if (opts.quantifiers->globalNegate__setByUser__)
      {
        throw OptionException(
            "global-negate not supported with old unsat cores");
      }
      Notice() << "SmtEngine: turning off global-negate to support old unsat "
                  "cores\n";
      opts.set(options::globalNegate, false);
    }

    if (options::bitvectorAig())
    {
      throw OptionException("bitblast-aig not supported with old unsat cores");
    }

    if (options::doITESimp())
    {
      throw OptionException("ITE simp not supported with old unsat cores");
    }
  }
  else
  {
    // by default, nonclausal simplification is off for QF_SAT
    if (!opts.smt->simplificationMode__setByUser__)
    {
      bool qf_sat = logic.isPure(THEORY_BOOL) && !logic.isQuantified();
      Trace("smt") << "setting simplification mode to <"
                   << logic.getLogicString() << "> " << (!qf_sat) << std::endl;
      // simplification=none works better for SMT LIB benchmarks with
      // quantifiers, not others opts.set(options::simplificationMode, qf_sat ||
      // quantifiers ? options::SimplificationMode::NONE :
      // options::SimplificationMode::BATCH);
      opts.set(options::simplificationMode, qf_sat
                                          ? options::SimplificationMode::NONE
                                          : options::SimplificationMode::BATCH);
    }
  }

  if (options::cegqiBv() && logic.isQuantified())
  {
    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      if (opts.bv->boolToBitvector__setByUser__)
      {
        throw OptionException(
            "bool-to-bv != off not supported with CBQI BV for quantified "
            "logics");
      }
      Notice() << "SmtEngine: turning off bool-to-bitvector to support CBQI BV"
               << std::endl;
      opts.set(options::boolToBitvector, options::BoolToBVMode::OFF);
    }
  }

  // cases where we need produce models
  if (!options::produceModels()
      && (options::produceAssignments() || options::sygusRewSynthCheck()
          || usesSygus))
  {
    Notice() << "SmtEngine: turning on produce-models" << std::endl;
    opts.set(options::produceModels, true);
  }

  /////////////////////////////////////////////////////////////////////////////
  // Theory widening
  //
  // Some theories imply the use of other theories to handle certain operators,
  // e.g. UF to handle partial functions.
  /////////////////////////////////////////////////////////////////////////////
  bool needsUf = false;
  // strings require LIA, UF; widen the logic
  if (logic.isTheoryEnabled(THEORY_STRINGS))
  {
    LogicInfo log(logic.getUnlockedCopy());
    // Strings requires arith for length constraints, and also UF
    needsUf = true;
    if (!logic.isTheoryEnabled(THEORY_ARITH) || logic.isDifferenceLogic())
    {
      Notice()
          << "Enabling linear integer arithmetic because strings are enabled"
          << std::endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    else if (!logic.areIntegersUsed())
    {
      Notice() << "Enabling integer arithmetic because strings are enabled"
               << std::endl;
      log.enableIntegers();
    }
    logic = log;
    logic.lock();
  }
  if (options::bvAbstraction())
  {
    // bv abstraction may require UF
    Notice() << "Enabling UF because bvAbstraction requires it." << std::endl;
    needsUf = true;
  }
  else if (options::preSkolemQuantNested()
           && opts.quantifiers->preSkolemQuantNested__setByUser__)
  {
    // if pre-skolem nested is explictly set, then we require UF. If it is
    // not explicitly set, it is disabled below if UF is not present.
    Notice() << "Enabling UF because preSkolemQuantNested requires it."
             << std::endl;
    needsUf = true;
  }
  if (needsUf
      // Arrays, datatypes and sets permit Boolean terms and thus require UF
      || logic.isTheoryEnabled(THEORY_ARRAYS)
      || logic.isTheoryEnabled(THEORY_DATATYPES)
      || logic.isTheoryEnabled(THEORY_SETS)
      || logic.isTheoryEnabled(THEORY_BAGS)
      // Non-linear arithmetic requires UF to deal with division/mod because
      // their expansion introduces UFs for the division/mod-by-zero case.
      // If we are eliminating non-linear arithmetic via solve-int-as-bv,
      // then this is not required, since non-linear arithmetic will be
      // eliminated altogether (or otherwise fail at preprocessing).
      || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
          && options::solveIntAsBV() == 0)
      // FP requires UF since there are multiple operators that are partially
      // defined (see http://smtlib.cs.uiowa.edu/papers/BTRW15.pdf for more
      // details).
      || logic.isTheoryEnabled(THEORY_FP))
  {
    if (!logic.isTheoryEnabled(THEORY_UF))
    {
      LogicInfo log(logic.getUnlockedCopy());
      if (!needsUf)
      {
        Notice() << "Enabling UF because " << logic << " requires it."
                 << std::endl;
      }
      log.enableTheory(THEORY_UF);
      logic = log;
      logic.lock();
    }
  }
  if (options::arithMLTrick())
  {
    if (!logic.areIntegersUsed())
    {
      // enable integers
      LogicInfo log(logic.getUnlockedCopy());
      Notice() << "Enabling integers because arithMLTrick requires it."
               << std::endl;
      log.enableIntegers();
      logic = log;
      logic.lock();
    }
  }
  /////////////////////////////////////////////////////////////////////////////

  // Set the options for the theoryOf
  if (!opts.theory->theoryOfMode__setByUser__)
  {
    if (logic.isSharingEnabled() && !logic.isTheoryEnabled(THEORY_BV)
        && !logic.isTheoryEnabled(THEORY_STRINGS)
        && !logic.isTheoryEnabled(THEORY_SETS)
        && !logic.isTheoryEnabled(THEORY_BAGS)
        && !(logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
             && !logic.isQuantified()))
    {
      Trace("smt") << "setting theoryof-mode to term-based" << std::endl;
      opts.set(options::theoryOfMode, options::TheoryOfMode::THEORY_OF_TERM_BASED);
    }
  }

  // by default, symmetry breaker is on only for non-incremental QF_UF
  if (!opts.uf->ufSymmetryBreaker__setByUser__)
  {
    bool qf_uf_noinc = logic.isPure(THEORY_UF) && !logic.isQuantified()
                       && !options::incrementalSolving() && !safeUnsatCores;
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf_noinc
                 << std::endl;
    opts.set(options::ufSymmetryBreaker, qf_uf_noinc);
  }

  // If in arrays, set the UF handler to arrays
  if (logic.isTheoryEnabled(THEORY_ARRAYS) && !options::ufHo()
      && !options::finiteModelFind()
      && (!logic.isQuantified()
          || (logic.isQuantified() && !logic.isTheoryEnabled(THEORY_UF))))
  {
    Theory::setUninterpretedSortOwner(THEORY_ARRAYS);
  }
  else
  {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }

  if (!opts.smt->simplifyWithCareEnabled__setByUser__)
  {
    bool qf_aufbv =
        !logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF) && logic.isTheoryEnabled(THEORY_BV);

    bool withCare = qf_aufbv;
    Trace("smt") << "setting ite simplify with care to " << withCare
                 << std::endl;
    opts.set(options::simplifyWithCareEnabled, withCare);
  }
  // Turn off array eager index splitting for QF_AUFLIA
  if (!opts.arrays->arraysEagerIndexSplitting__setByUser__)
  {
    if (not logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF)
        && logic.isTheoryEnabled(THEORY_ARITH))
    {
      Trace("smt") << "setting array eager index splitting to false"
                   << std::endl;
      opts.set(options::arraysEagerIndexSplitting, false);
    }
  }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if (!opts.smt->repeatSimp__setByUser__)
  {
    bool repeatSimp = !logic.isQuantified()
                      && (logic.isTheoryEnabled(THEORY_ARRAYS)
                          && logic.isTheoryEnabled(THEORY_UF)
                          && logic.isTheoryEnabled(THEORY_BV))
                      && !safeUnsatCores;
    Trace("smt") << "setting repeat simplification to " << repeatSimp
                 << std::endl;
    opts.set(options::repeatSimp, repeatSimp);
  }

  if (options::boolToBitvector() == options::BoolToBVMode::ALL
      && !logic.isTheoryEnabled(THEORY_BV))
  {
    if (opts.bv->boolToBitvector__setByUser__)
    {
      throw OptionException(
          "bool-to-bv=all not supported for non-bitvector logics.");
    }
    Notice() << "SmtEngine: turning off bool-to-bv for non-bv logic: "
             << logic.getLogicString() << std::endl;
    opts.set(options::boolToBitvector, options::BoolToBVMode::OFF);
  }

  if (!opts.bv->bvEagerExplanations__setByUser__
      && logic.isTheoryEnabled(THEORY_ARRAYS)
      && logic.isTheoryEnabled(THEORY_BV))
  {
    Trace("smt") << "enabling eager bit-vector explanations " << std::endl;
    opts.set(options::bvEagerExplanations, true);
  }

  // Turn on arith rewrite equalities only for pure arithmetic
  if (!opts.arith->arithRewriteEq__setByUser__)
  {
    bool arithRewriteEq =
        logic.isPure(THEORY_ARITH) && logic.isLinear() && !logic.isQuantified();
    Trace("smt") << "setting arith rewrite equalities " << arithRewriteEq
                 << std::endl;
    opts.set(options::arithRewriteEq, arithRewriteEq);
  }
  if (!opts.arith->arithHeuristicPivots__setByUser__)
  {
    int16_t heuristicPivots = 5;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      if (logic.isDifferenceLogic())
      {
        heuristicPivots = -1;
      }
      else if (!logic.areIntegersUsed())
      {
        heuristicPivots = 0;
      }
    }
    Trace("smt") << "setting arithHeuristicPivots  " << heuristicPivots
                 << std::endl;
    opts.set(options::arithHeuristicPivots, heuristicPivots);
  }
  if (!opts.arith->arithPivotThreshold__setByUser__)
  {
    uint16_t pivotThreshold = 2;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      if (logic.isDifferenceLogic())
      {
        pivotThreshold = 16;
      }
    }
    Trace("smt") << "setting arith arithPivotThreshold  " << pivotThreshold
                 << std::endl;
    opts.set(options::arithPivotThreshold, pivotThreshold);
  }
  if (!opts.arith->arithStandardCheckVarOrderPivots__setByUser__)
  {
    int16_t varOrderPivots = -1;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      varOrderPivots = 200;
    }
    Trace("smt") << "setting arithStandardCheckVarOrderPivots  "
                 << varOrderPivots << std::endl;
    opts.set(options::arithStandardCheckVarOrderPivots, varOrderPivots);
  }
  if (logic.isPure(THEORY_ARITH) && !logic.areRealsUsed())
  {
    if (!opts.arith->nlExtTangentPlanesInterleave__setByUser__)
    {
      Trace("smt") << "setting nlExtTangentPlanesInterleave to true"
                   << std::endl;
      opts.set(options::nlExtTangentPlanesInterleave, true);
    }
  }

  // Set decision mode based on logic (if not set by user)
  if (!opts.decision->decisionMode__setByUser__)
  {
    options::DecisionMode decMode =
        // anything that uses sygus uses internal
        usesSygus ? options::DecisionMode::INTERNAL :
                  // ALL
            logic.hasEverything()
                ? options::DecisionMode::JUSTIFICATION
                : (  // QF_BV
                      (not logic.isQuantified() && logic.isPure(THEORY_BV)) ||
                              // QF_AUFBV or QF_ABV or QF_UFBV
                              (not logic.isQuantified()
                               && (logic.isTheoryEnabled(THEORY_ARRAYS)
                                   || logic.isTheoryEnabled(THEORY_UF))
                               && logic.isTheoryEnabled(THEORY_BV))
                              ||
                              // QF_AUFLIA (and may be ends up enabling
                              // QF_AUFLRA?)
                              (not logic.isQuantified()
                               && logic.isTheoryEnabled(THEORY_ARRAYS)
                               && logic.isTheoryEnabled(THEORY_UF)
                               && logic.isTheoryEnabled(THEORY_ARITH))
                              ||
                              // QF_LRA
                              (not logic.isQuantified()
                               && logic.isPure(THEORY_ARITH) && logic.isLinear()
                               && !logic.isDifferenceLogic()
                               && !logic.areIntegersUsed())
                              ||
                              // Quantifiers
                              logic.isQuantified() ||
                              // Strings
                              logic.isTheoryEnabled(THEORY_STRINGS)
                          ? options::DecisionMode::JUSTIFICATION
                          : options::DecisionMode::INTERNAL);

    bool stoponly =
        // ALL
        logic.hasEverything() || logic.isTheoryEnabled(THEORY_STRINGS)
            ? false
            : (  // QF_AUFLIA
                  (not logic.isQuantified()
                   && logic.isTheoryEnabled(THEORY_ARRAYS)
                   && logic.isTheoryEnabled(THEORY_UF)
                   && logic.isTheoryEnabled(THEORY_ARITH))
                          ||
                          // QF_LRA
                          (not logic.isQuantified()
                           && logic.isPure(THEORY_ARITH) && logic.isLinear()
                           && !logic.isDifferenceLogic()
                           && !logic.areIntegersUsed())
                      ? true
                      : false);

    Trace("smt") << "setting decision mode to " << decMode << std::endl;
    opts.set(options::decisionMode, decMode);
    opts.set(options::decisionStopOnly, stoponly);
  }
  if (options::incrementalSolving())
  {
    // disable modes not supported by incremental
    opts.set(options::sortInference, false);
    opts.set(options::ufssFairnessMonotone, false);
    opts.set(options::globalNegate, false);
    opts.set(options::bvAbstraction, false);
    opts.set(options::arithMLTrick, false);
  }
  if (logic.hasCardinalityConstraints())
  {
    // must have finite model finding on
    opts.set(options::finiteModelFind, true);
  }

  if (options::instMaxLevel() != -1)
  {
    Notice() << "SmtEngine: turning off cbqi to support instMaxLevel"
             << std::endl;
    opts.set(options::cegqi, false);
  }

  if ((opts.quantifiers->fmfBoundLazy__setByUser__ && options::fmfBoundInt())
      || (opts.quantifiers->fmfBoundInt__setByUser__ && options::fmfBoundInt()))
  {
    opts.set(options::fmfBound, true);
  }
  // now have determined whether fmfBoundInt is on/off
  // apply fmfBoundInt options
  if (options::fmfBound())
  {
    if (!opts.quantifiers->mbqiMode__setByUser__
        || (options::mbqiMode() != options::MbqiMode::NONE
            && options::mbqiMode() != options::MbqiMode::FMC))
    {
      // if bounded integers are set, use no MBQI by default
      opts.set(options::mbqiMode, options::MbqiMode::NONE);
    }
    if (!opts.quantifiers->prenexQuantUser__setByUser__)
    {
      opts.set(options::prenexQuant, options::PrenexQuantMode::NONE);
    }
  }
  if (options::ufHo())
  {
    // if higher-order, then current variants of model-based instantiation
    // cannot be used
    if (options::mbqiMode() != options::MbqiMode::NONE)
    {
      opts.set(options::mbqiMode, options::MbqiMode::NONE);
    }
    if (!opts.quantifiers->hoElimStoreAx__setByUser__)
    {
      // by default, use store axioms only if --ho-elim is set
      opts.set(options::hoElimStoreAx, options::hoElim());
    }
    if (!options::assignFunctionValues())
    {
      // must assign function values
      opts.set(options::assignFunctionValues, true);
    }
    // Cannot use macros, since lambda lifting and macro elimination are inverse
    // operations.
    if (options::macrosQuant())
    {
      opts.set(options::macrosQuant, false);
    }
  }
  if (options::fmfFunWellDefinedRelevant())
  {
    if (!opts.quantifiers->fmfFunWellDefined__setByUser__)
    {
      opts.set(options::fmfFunWellDefined, true);
    }
  }
  if (options::fmfFunWellDefined())
  {
    if (!opts.quantifiers->finiteModelFind__setByUser__)
    {
      opts.set(options::finiteModelFind, true);
    }
  }

  // now, have determined whether finite model find is on/off
  // apply finite model finding options
  if (options::finiteModelFind())
  {
    // apply conservative quantifiers splitting
    if (!opts.quantifiers->quantDynamicSplit__setByUser__)
    {
      opts.set(options::quantDynamicSplit, options::QuantDSplitMode::DEFAULT);
    }
    if (!opts.quantifiers->eMatching__setByUser__)
    {
      opts.set(options::eMatching, options::fmfInstEngine());
    }
    if (!opts.quantifiers->instWhenMode__setByUser__)
    {
      // instantiate only on last call
      if (options::eMatching())
      {
        opts.set(options::instWhenMode, options::InstWhenMode::LAST_CALL);
      }
    }
  }

  // apply sygus options
  // if we are attempting to rewrite everything to SyGuS, use sygus()
  if (usesSygus)
  {
    if (!options::sygus())
    {
      Trace("smt") << "turning on sygus" << std::endl;
    }
    opts.set(options::sygus, true);
    // must use Ferrante/Rackoff for real arithmetic
    if (!opts.quantifiers->cegqiMidpoint__setByUser__)
    {
      opts.set(options::cegqiMidpoint, true);
    }
    // must disable cegqi-bv since it may introduce witness terms, which
    // cannot appear in synthesis solutions
    if (!opts.quantifiers->cegqiBv__setByUser__)
    {
      opts.set(options::cegqiBv, false);
    }
    if (options::sygusRepairConst())
    {
      if (!opts.quantifiers->cegqi__setByUser__)
      {
        opts.set(options::cegqi, true);
      }
    }
    if (options::sygusInference())
    {
      // optimization: apply preskolemization, makes it succeed more often
      if (!opts.quantifiers->preSkolemQuant__setByUser__)
      {
        opts.set(options::preSkolemQuant, true);
      }
      if (!opts.quantifiers->preSkolemQuantNested__setByUser__)
      {
        opts.set(options::preSkolemQuantNested, true);
      }
    }
    // counterexample-guided instantiation for sygus
    if (!opts.quantifiers->cegqiSingleInvMode__setByUser__)
    {
      opts.set(options::cegqiSingleInvMode, options::CegqiSingleInvMode::USE);
    }
    if (!opts.quantifiers->quantConflictFind__setByUser__)
    {
      opts.set(options::quantConflictFind, false);
    }
    if (!opts.quantifiers->instNoEntail__setByUser__)
    {
      opts.set(options::instNoEntail, false);
    }
    if (!opts.quantifiers->cegqiFullEffort__setByUser__)
    {
      // should use full effort cbqi for single invocation and repair const
      opts.set(options::cegqiFullEffort, true);
    }
    if (options::sygusRew())
    {
      opts.set(options::sygusRewSynth, true);
      opts.set(options::sygusRewVerify, true);
    }
    if (options::sygusRewSynthInput())
    {
      // If we are using synthesis rewrite rules from input, we use
      // sygusRewSynth after preprocessing. See passes/synth_rew_rules.h for
      // details on this technique.
      opts.set(options::sygusRewSynth, true);
      // we should not use the extended rewriter, since we are interested
      // in rewrites that are not in the main rewriter
      if (!opts.quantifiers->sygusExtRew__setByUser__)
      {
        opts.set(options::sygusExtRew, false);
      }
    }
    // Whether we must use "basic" sygus algorithms. A non-basic sygus algorithm
    // is one that is specialized for returning a single solution. Non-basic
    // sygus algorithms currently include the PBE solver, UNIF+PI, static
    // template inference for invariant synthesis, and single invocation
    // techniques.
    bool reqBasicSygus = false;
    if (options::produceAbducts())
    {
      // if doing abduction, we should filter strong solutions
      if (!opts.quantifiers->sygusFilterSolMode__setByUser__)
      {
        opts.set(options::sygusFilterSolMode, options::SygusFilterSolMode::STRONG);
      }
      // we must use basic sygus algorithms, since e.g. we require checking
      // a sygus side condition for consistency with axioms.
      reqBasicSygus = true;
    }
    if (options::sygusRewSynth() || options::sygusRewVerify()
        || options::sygusQueryGen())
    {
      // rewrite rule synthesis implies that sygus stream must be true
      opts.set(options::sygusStream, true);
    }
    if (options::sygusStream() || options::incrementalSolving())
    {
      // Streaming and incremental mode are incompatible with techniques that
      // focus the search towards finding a single solution.
      reqBasicSygus = true;
    }
    // Now, disable options for non-basic sygus algorithms, if necessary.
    if (reqBasicSygus)
    {
      if (!opts.quantifiers->sygusUnifPbe__setByUser__)
      {
        opts.set(options::sygusUnifPbe, false);
      }
      if (opts.quantifiers->sygusUnifPi__setByUser__)
      {
        opts.set(options::sygusUnifPi, options::SygusUnifPiMode::NONE);
      }
      if (!opts.quantifiers->sygusInvTemplMode__setByUser__)
      {
        opts.set(options::sygusInvTemplMode, options::SygusInvTemplMode::NONE);
      }
      if (!opts.quantifiers->cegqiSingleInvMode__setByUser__)
      {
        opts.set(options::cegqiSingleInvMode, options::CegqiSingleInvMode::NONE);
      }
    }
    if (!opts.datatypes->dtRewriteErrorSel__setByUser__)
    {
      opts.set(options::dtRewriteErrorSel, true);
    }
    // do not miniscope
    if (!opts.quantifiers->miniscopeQuant__setByUser__)
    {
      opts.set(options::miniscopeQuant, false);
    }
    if (!opts.quantifiers->miniscopeQuantFreeVar__setByUser__)
    {
      opts.set(options::miniscopeQuantFreeVar, false);
    }
    if (!opts.quantifiers->quantSplit__setByUser__)
    {
      opts.set(options::quantSplit, false);
    }
    // do not do macros
    if (!opts.quantifiers->macrosQuant__setByUser__)
    {
      opts.set(options::macrosQuant, false);
    }
    // use tangent planes by default, since we want to put effort into
    // the verification step for sygus queries with non-linear arithmetic
    if (!opts.arith->nlExtTangentPlanes__setByUser__)
    {
      opts.set(options::nlExtTangentPlanes, true);
    }
  }
  // counterexample-guided instantiation for non-sygus
  // enable if any possible quantifiers with arithmetic, datatypes or bitvectors
  if ((logic.isQuantified()
       && (logic.isTheoryEnabled(THEORY_ARITH)
           || logic.isTheoryEnabled(THEORY_DATATYPES)
           || logic.isTheoryEnabled(THEORY_BV)
           || logic.isTheoryEnabled(THEORY_FP)))
      || options::cegqiAll())
  {
    if (!opts.quantifiers->cegqi__setByUser__)
    {
      opts.set(options::cegqi, true);
    }
    // check whether we should apply full cbqi
    if (logic.isPure(THEORY_BV))
    {
      if (!opts.quantifiers->cegqiFullEffort__setByUser__)
      {
        opts.set(options::cegqiFullEffort, true);
      }
    }
  }
  if (options::cegqi())
  {
    if (options::incrementalSolving())
    {
      // cannot do nested quantifier elimination in incremental mode
      opts.set(options::cegqiNestedQE, false);
    }
    if (logic.isPure(THEORY_ARITH) || logic.isPure(THEORY_BV))
    {
      if (!opts.quantifiers->quantConflictFind__setByUser__)
      {
        opts.set(options::quantConflictFind, false);
      }
      if (!opts.quantifiers->instNoEntail__setByUser__)
      {
        opts.set(options::instNoEntail, false);
      }
      if (!opts.quantifiers->instWhenMode__setByUser__ && options::cegqiModel())
      {
        // only instantiation should happen at last call when model is avaiable
        opts.set(options::instWhenMode, options::InstWhenMode::LAST_CALL);
      }
    }
    else
    {
      // only supported in pure arithmetic or pure BV
      opts.set(options::cegqiNestedQE, false);
    }
    if (options::globalNegate())
    {
      if (!opts.quantifiers->prenexQuant__setByUser__)
      {
        opts.set(options::prenexQuant, options::PrenexQuantMode::NONE);
      }
    }
  }
  // implied options...
  if (options::strictTriggers())
  {
    if (!opts.quantifiers->userPatternsQuant__setByUser__)
    {
      opts.set(options::userPatternsQuant, options::UserPatMode::TRUST);
    }
  }
  if (opts.quantifiers->qcfMode__setByUser__ || options::qcfTConstraint())
  {
    opts.set(options::quantConflictFind, true);
  }
  if (options::cegqiNestedQE())
  {
    opts.set(options::prenexQuantUser, true);
    if (!opts.quantifiers->preSkolemQuant__setByUser__)
    {
      opts.set(options::preSkolemQuant, true);
    }
  }
  // for induction techniques
  if (options::quantInduction())
  {
    if (!opts.quantifiers->dtStcInduction__setByUser__)
    {
      opts.set(options::dtStcInduction, true);
    }
    if (!opts.quantifiers->intWfInduction__setByUser__)
    {
      opts.set(options::intWfInduction, true);
    }
  }
  if (options::dtStcInduction())
  {
    // try to remove ITEs from quantified formulas
    if (!opts.quantifiers->iteDtTesterSplitQuant__setByUser__)
    {
      opts.set(options::iteDtTesterSplitQuant, true);
    }
    if (!opts.quantifiers->iteLiftQuant__setByUser__)
    {
      opts.set(options::iteLiftQuant, options::IteLiftQuantMode::ALL);
    }
  }
  if (options::intWfInduction())
  {
    if (!opts.quantifiers->purifyTriggers__setByUser__)
    {
      opts.set(options::purifyTriggers, true);
    }
  }
  if (options::conjectureNoFilter())
  {
    if (!opts.quantifiers->conjectureFilterActiveTerms__setByUser__)
    {
      opts.set(options::conjectureFilterActiveTerms, false);
    }
    if (!opts.quantifiers->conjectureFilterCanonical__setByUser__)
    {
      opts.set(options::conjectureFilterCanonical, false);
    }
    if (!opts.quantifiers->conjectureFilterModel__setByUser__)
    {
      opts.set(options::conjectureFilterModel, false);
    }
  }
  if (opts.quantifiers->conjectureGenPerRound__setByUser__)
  {
    if (options::conjectureGenPerRound() > 0)
    {
      opts.set(options::conjectureGen, true);
    }
    else
    {
      opts.set(options::conjectureGen, false);
    }
  }
  // can't pre-skolemize nested quantifiers without UF theory
  if (!logic.isTheoryEnabled(THEORY_UF) && options::preSkolemQuant())
  {
    if (!opts.quantifiers->preSkolemQuantNested__setByUser__)
    {
      opts.set(options::preSkolemQuantNested, false);
    }
  }
  if (!logic.isTheoryEnabled(THEORY_DATATYPES))
  {
    opts.set(options::quantDynamicSplit, options::QuantDSplitMode::NONE);
  }

  // until bugs 371,431 are fixed
  if (!opts.prop->minisatUseElim__setByUser__)
  {
    // cannot use minisat elimination for logics where a theory solver
    // introduces new literals into the search. This includes quantifiers
    // (quantifier instantiation), and the lemma schemas used in non-linear
    // and sets. We also can't use it if models are enabled.
    if (logic.isTheoryEnabled(THEORY_SETS)
        || logic.isTheoryEnabled(THEORY_BAGS)
        || logic.isQuantified()
        || options::produceModels() || options::produceAssignments()
        || options::checkModels()
        || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
    {
      opts.set(options::minisatUseElim, false);
    }
  }

  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
      && options::nlRlvMode() != options::NlRlvMode::NONE)
  {
    if (!options::relevanceFilter())
    {
      if (opts.theory->relevanceFilter__setByUser__)
      {
        Warning() << "SmtEngine: turning on relevance filtering to support "
                     "--nl-ext-rlv="
                  << options::nlRlvMode() << std::endl;
      }
      // must use relevance filtering techniques
      opts.set(options::relevanceFilter, true);
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (options::produceModels() || options::produceAssignments()
      || options::checkModels())
  {
    opts.set(options::arraysOptimizeLinear, false);
  }

  if (!options::bitvectorEqualitySolver())
  {
    if (options::bvLazyRewriteExtf())
    {
      if (opts.bv->bvLazyRewriteExtf__setByUser__)
      {
        throw OptionException(
            "--bv-lazy-rewrite-extf requires --bv-eq-solver to be set");
      }
    }
    Trace("smt")
        << "disabling bvLazyRewriteExtf since equality solver is disabled"
        << std::endl;
    opts.set(options::bvLazyRewriteExtf, false);
  }

  if (options::stringFMF() && !opts.strings->stringProcessLoopMode__setByUser__)
  {
    Trace("smt") << "settting stringProcessLoopMode to 'simple' since "
                    "--strings-fmf enabled"
                 << std::endl;
    opts.set(options::stringProcessLoopMode, options::ProcessLoopMode::SIMPLE);
  }

  // !!! All options that require disabling models go here
  bool disableModels = false;
  std::string sOptNoModel;
  if (opts.smt->unconstrainedSimp__setByUser__ && options::unconstrainedSimp())
  {
    disableModels = true;
    sOptNoModel = "unconstrained-simp";
  }
  else if (options::sortInference())
  {
    disableModels = true;
    sOptNoModel = "sort-inference";
  }
  else if (options::minisatUseElim())
  {
    disableModels = true;
    sOptNoModel = "minisat-elimination";
  }
  else if (options::globalNegate())
  {
    disableModels = true;
    sOptNoModel = "global-negate";
  }
  if (disableModels)
  {
    if (options::produceModels())
    {
      if (opts.smt->produceModels__setByUser__)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel << " with model generation.";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-models to support "
               << sOptNoModel << std::endl;
      opts.set(options::produceModels, false);
    }
    if (options::produceAssignments())
    {
      if (opts.smt->produceAssignments__setByUser__)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (produce-assignments).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-assignments to support "
               << sOptNoModel << std::endl;
      opts.set(options::produceAssignments, false);
    }
    if (options::checkModels())
    {
      if (opts.smt->checkModels__setByUser__)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (check-models).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off check-models to support "
               << sOptNoModel << std::endl;
      opts.set(options::checkModels, false);
    }
  }

  if (options::bitblastMode() == options::BitblastMode::EAGER
      && !logic.isPure(THEORY_BV) && logic.getLogicString() != "QF_UFBV"
      && logic.getLogicString() != "QF_ABV")
  {
    throw OptionException(
        "Eager bit-blasting does not currently support theory combination. "
        "Note that in a QF_BV problem UF symbols can be introduced for "
        "division. "
        "Try --bv-div-zero-const to interpret division by zero as a constant.");
  }

  if (logic == LogicInfo("QF_UFNRA"))
  {
#ifdef CVC5_USE_POLY
    if (!options::nlCad() && !opts.arith->nlCad__setByUser__)
    {
      opts.set(options::nlCad, true);
      if (!opts.arith->nlExt__setByUser__)
      {
        opts.set(options::nlExt, false);
      }
      if (!opts.arith->nlRlvMode__setByUser__)
      {
        opts.set(options::nlRlvMode, options::NlRlvMode::INTERLEAVE);
      }
    }
#endif
  }
#ifndef CVC5_USE_POLY
  if (options::nlCad())
  {
    if (opts.arith->nlCad__setByUser__)
    {
      std::stringstream ss;
      ss << "Cannot use " << options::nlCad.name << " without configuring with --poly.";
      throw OptionException(ss.str());
    }
    else
    {
      Notice() << "Cannot use --" << options::nlCad.name
               << " without configuring with --poly." << std::endl;
      opts.set(options::nlCad, false);
      opts.set(options::nlExt, true);
    }
  }
#endif
}

}  // namespace smt
}  // namespace cvc5
