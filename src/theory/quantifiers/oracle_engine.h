/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Oracle engine for SMTO
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ORACLE_ENGINE_H
#define CVC5__THEORY__QUANTIFIERS__ORACLE_ENGINE_H

#include "theory/quantifiers/oracle_checker.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Oracle engine
 */
class OracleEngine : public QuantifiersModule
{
 public:
  OracleEngine(Env& env,
               QuantifiersState& qs,
               QuantifiersInferenceManager& qim,
               QuantifiersRegistry& qr,
               TermRegistry& tr);
  ~OracleEngine() {}
  /** Presolve */
  void presolve() override;
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Needs model. */
  QEffort needsModel(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /**
   * Check was complete for quantified formula q, return true if we can say
   * "sat" provided that q is currently asserted.
   */
  bool checkCompleteFor(Node q) override;
  /** check ownership */
  void checkOwnership(Node q) override;
  /** Identify. */
  std::string identify() const override;

  /** Declare oracle fun */
  void declareOracleFun(Node f, const std::string& binName);
  /** Get the list of all declared oracle functions */
  std::vector<Node> getOracleFuns() const;

  /** Make an oracle interface quantifier */
  static Node mkOracleInterface(const std::vector<Node>& inputs,
                                const std::vector<Node>& outputs,
                                Node assume,
                                Node constraint,
                                const std::string& binName);
  /** get oracle interface, returns true if q is an oracle interface quantifier
   * (constructed by the above method). Obtains the arguments for which q is
   * constructed. */
  bool getOracleInterface(Node q,
                          std::vector<Node>& inputs,
                          std::vector<Node>& outputs,
                          Node& assume,
                          Node& constraint,
                          std::string& binName);

 private:
  /** The oracle functions (user-context dependent) */
  context::CDList<Node> d_oracleFuns;
  /** Pointer to the oracle checker */
  OracleChecker* d_ochecker;
  bool d_consistencyCheckPassed = false;
  bool d_checkedAllOracles = false;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif