/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A theory engine module based on a user plugin.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__PLUGIN_MODULE_H
#define CVC5__THEORY__PLUGIN_MODULE_H

#include <vector>

#include "expr/plugin.h"
#include "theory/theory_engine_module.h"

namespace cvc5::internal {

namespace theory {

class PluginModule : public TheoryEngineModule
{
 public:
  PluginModule(Env& env, TheoryEngine* theoryEngine, Plugin* p);

  /**
   * Check at the given effort.
   */
  void check(Theory::Effort e) override;

 private:
  /** The plugin */
  Plugin* d_plugin;
};
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__PARTITION__GENERATOR_H */