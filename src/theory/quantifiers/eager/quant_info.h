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
 * Quantifier info for eager instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__QUANT_INFO_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__QUANT_INFO_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/eager/trigger_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbEager;
class QuantifiersRegistry;

namespace eager {

class QuantInfo
{
 public:
  QuantInfo(TermDbEager& tde);
  /** Initialize this for quantified formula q */
  void initialize(QuantifiersRegistry& qr, const Node& q);
  /** Set that the quantified formula for this class is asserted */
  void notifyAsserted();
  /** Get quantified formula */
  Node getQuant() const { return d_quant; }
  /** Is the quantified formula asserted? */
  bool isAsserted() const { return d_asserted.get(); }
  /** Notify that a trigger has been assigned a status */
  TriggerStatus notifyTriggerStatus(TriggerInfo* tinfo, TriggerStatus status);

 private:
  /** The quantified formula */
  Node d_quant;
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** List of triggers */
  std::vector<TriggerInfo*> d_triggers;
  /** Is asserted */
  context::CDO<bool> d_asserted;
  /** The index in d_triggers that is inactive */
  context::CDO<size_t> d_tinactiveIndex;
  /** The current status */
  context::CDO<TriggerStatus> d_tstatus;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif