/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model normal form finder for strings
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__DEFAULT_MODEL_CONS_H
#define CVC5__THEORY__STRINGS__DEFAULT_MODEL_CONS_H

#include "smt/env_obj.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/solver_state.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Default model construction for strings
 */
class ModelConsDefault : public ModelCons
{
 public:
  ModelConsDefault(Env& env, SolverState& state, CoreSolver& csolver);
  virtual ~ModelConsDefault() {}

  /** Get string representatives from */
  void getStringRepresentativesFrom(
      const std::set<Node>& termSet,
      std::unordered_set<TypeNode>& repTypes,
      std::map<TypeNode, std::unordered_set<Node>>& repSet,
      std::vector<Node>& auxEq) override;
  /** Separate by length */
  void separateByLength(const std::vector<Node>& ns,
                        std::vector<std::vector<Node>>& cols,
                        std::vector<Node>& lts) override;
  /** Get the normal form */
  std::vector<Node> getNormalForm(Node n) override;

 protected:
  /** The solver state object */
  SolverState& d_state;
  /** The core solver */
  CoreSolver& d_csolver;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__MODEL_CONS_H */