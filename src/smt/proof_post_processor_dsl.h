/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for final processing proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_POST_PROCESSOR_DSL_H
#define CVC5__SMT__PROOF_POST_PROCESSOR_DSL_H

#include <map>
#include <sstream>
#include <unordered_set>

#include "proof/proof_node_updater.h"
#include "proof/trust_id.h"
#include "rewriter/rewrite_db_proof_cons.h"
#include "rewriter/rewrites.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace smt {

/** Final callback class, for stats and pedantic checking */
class ProofPostprocessDsl : protected EnvObj, public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessDsl(Env& env, rewriter::RewriteDb* rdb);

  void reconstruct(std::unordered_set<std::shared_ptr<ProofNode>>& pfs);

  bool reconstruct(std::shared_ptr<ProofNode>& pf);

  /** Should proof pn be updated? */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Update the proof rule application. */
  bool update(Node res,
              ProofRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  Node d_true;
  /** The rewrite database proof generator */
  rewriter::RewriteDbProofCons d_rdbPc;
  /** Is provable? */
  bool isProvable(const Node& n,
                  std::unordered_set<rewriter::DslProofRule>& ucRules);
  /** The embedded axioms */
  std::vector<Node> d_embedAxioms;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif