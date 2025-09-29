/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Lydia Kondylidou, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for augmenting model-based instantiations via fast sygus enumeration.
 */

#include "theory/quantifiers/mbqi_enum.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "printer/smt2/smt2_printer.h"
#include "smt/set_defaults.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/inst_strategy_mbqi.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/smt_engine_subsolver.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class MbqiEnumTermEnumeratorCallback : protected EnvObj,
                                       public SygusTermEnumeratorCallback
{
 public:
  MbqiEnumTermEnumeratorCallback(Env& env) : EnvObj(env) {}
  virtual ~MbqiEnumTermEnumeratorCallback() {}
  /**
   */
  bool addTerm(const Node& n, std::unordered_set<Node>& bterms) override
  {
    Node bn = datatypes::utils::sygusToBuiltin(n);
    bn = extendedRewrite(bn);
    if (bterms.find(bn) != bterms.end())
    {
      return false;
    }
    if (bn.getKind() == Kind::WITNESS)
    {
      if (!expr::hasSubterm(bn[1], bn[0][0]))
      {
        // always allow witness x. true ?
        // if (!bn[1].isConst() || !bn[1].getConst<bool>())
        //{
        //  return false;
        //}
        return false;
      }
    }
    bterms.insert(bn);
    return true;
  }
};

bool shouldEnumerate(const Options& opts, const TypeNode& tn)
{
  // It may make sense to enumerate choice for FO uninterpreted sorts, but
  // seems to not work well in practice.
  //if (tn.isUninterpretedSort() && !opts.quantifiers.mbqiEnumChoiceGrammar)
  if (tn.isUninterpretedSort())
  {
    return false;
  }
  return true;
}

void MVarInfo::initialize(Env& env,
                          const Node& q,
                          const Node& v,
                          const std::vector<Node>& etrules)
{
  NodeManager* nm = env.getNodeManager();
  TypeNode tn = v.getType();
  Assert(shouldEnumerate(env.getOptions(), tn));
  TypeNode retType = tn;
  std::vector<Node> trules;
  if (tn.isFunction())
  {
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    retType = tn.getRangeType();
    std::vector<Node> vs;
    for (const TypeNode& tnc : argTypes)
    {
      Node vc = NodeManager::mkBoundVar(tnc);
      vs.push_back(vc);
    }
    d_lamVars = nm->mkNode(Kind::BOUND_VAR_LIST, vs);
    trules.insert(trules.end(), vs.begin(), vs.end());
  }
  // include free symbols from quantified formula
  if (env.getOptions().quantifiers.mbqiEnumFreeSymsGrammar)
  {
    std::unordered_set<Node> syms;
    expr::getSymbols(q[1], syms);
    trules.insert(trules.end(), syms.begin(), syms.end());
  }
  // include external terminal rules
  for (const Node& symbol : etrules)
  {
    if (std::find(trules.begin(), trules.end(), symbol) == trules.end())
    {
      trules.push_back(symbol);
    }
  }
  Trace("mbqi-enum-grammar") << "Symbols: " << trules << std::endl;
  SygusGrammarCons sgc;
  Node bvl;
  TypeNode tng = sgc.mkDefaultSygusType(env, retType, bvl, trules);
  if (TraceIsOn("mbqi-enum"))
  {
    Trace("mbqi-enum") << "Enumerate terms for " << retType;
    if (!d_lamVars.isNull())
    {
      Trace("mbqi-enum") << ", variable list " << d_lamVars;
    }
    Trace("mbqi-enum") << std::endl;
    Trace("mbqi-enum-grammar") << "Based on grammar:" << std::endl;
    Trace("mbqi-enum-grammar")
        << printer::smt2::Smt2Printer::sygusGrammarString(tng) << std::endl;
  }
  TypeNode tuse = tng;
  const Options& opts = env.getOptions();

  // include quantifiers in the grammar (only for predicates)
  if (opts.quantifiers.mbqiEnumQuantGrammar && retType.isBoolean())
  {
    SygusGrammar sgg({}, tng);
    const std::vector<Node>& nts = sgg.getNtSyms();
    std::vector<Node> ntAll = nts;

    // multiple subgrammars per type (arg type -> list of subgrammars)
    std::map<TypeNode, std::vector<std::shared_ptr<SygusGrammar>>> typeToSubGrammars;
    // map function-type -> FORALL node to attach (body will reference the subgrammar non-terminals)
    std::map<TypeNode, Node> typeToQuantRule;
    // keep a list of all subgrammars we create (so we can add their rules into sgcom)
    std::vector<std::shared_ptr<SygusGrammar>> allSubGrammars;

    for (const Node& nt : nts)
    {
      TypeNode ntt = nt.getType();
      if (!ntt.isFunction())
      {
        continue;
      }

      std::vector<TypeNode> argTypes = ntt.getArgTypes();
      TypeNode ret = ntt.getRangeType();

      std::vector<Node> baseTrules = trules;
      std::vector<Node> qvars;      // bound variables for FORALL
      std::vector<Node> varNTs;     // nonterminals for arguments (from subgrammars)

      // create subgrammars for each argument type (re-use or create new)
      for (size_t i = 0; i < argTypes.size(); ++i)
      {
        TypeNode at = argTypes[i];
        Node xi = nm->mkBoundVar("x" + std::to_string(i), at);
        qvars.push_back(xi);

        std::shared_ptr<SygusGrammar> subG;
        if (!typeToSubGrammars[at].empty())
        {
          // reuse last subgrammar for this arg type (you already wanted multiple subgrammars)
          subG = typeToSubGrammars[at].back();
          Trace("mbqi-enum-quant-grammar")
              << "  reuse last subgrammar for arg " << i << ", type: " << at << std::endl;
        }
        else
        {
          // create a fresh subgrammar for this argument type that includes xi as a terminal
          std::vector<Node> subtrules = baseTrules;
          subtrules.push_back(xi);  // include the new bound variable as a terminal

          Trace("mbqi-enum-quant-grammar")
              << "Add bound variable " << xi << " to grammar for type " << at << std::endl;
          Trace("mbqi-enum-quant-grammar")
              << "Make quantifiers grammar " << subtrules << std::endl;

          // build a SyGuS type for this subgrammar (returns a TypeNode sygus datatype)
          TypeNode tnb = sgc.mkDefaultSygusType(env, ret, bvl, subtrules);
          Trace("mbqi-enum-quant-grammar") << "Quantifiers grammar:" << std::endl;
          Trace("mbqi-enum-quant-grammar")
              << printer::smt2::Smt2Printer::sygusGrammarString(tnb) << std::endl;

          // create an actual SygusGrammar object for this subgrammar
          subG = std::make_shared<SygusGrammar>(std::vector<Node>(), tnb);
          Assert(!subG->getNtSyms().empty());

          // remember it under this argument type
          typeToSubGrammars[at].push_back(subG);
          // also remember in global list for merging later
          allSubGrammars.push_back(subG);

          // collect its nonterminals into ntAll so the combined grammar mentions them
          const std::vector<Node>& ntsb = subG->getNtSyms();
          ntAll.insert(ntAll.end(), ntsb.begin(), ntsb.end());

          Trace("mbqi-enum-quant-grammar")
              << "  created var-subgrammar for arg " << i << ", sub-NTs: " << ntsb << std::endl;
        }

        // find the non-terminal in the subgrammar corresponding to the argument type (the var NT)
        Node varNt;
        for (const Node& snt : subG->getNtSyms())
        {
          if (snt.getType() == at)
          {
            varNt = snt;
            break;
          }
        }
        Assert(!varNt.isNull());
        varNTs.push_back(varNt);
      }

      // create Boolean body subgrammar that can reference the var-NTs
      std::vector<Node> trBody = baseTrules;
      trBody.insert(trBody.end(), varNTs.begin(), varNTs.end());
      TypeNode tnbBody = sgc.mkDefaultSygusType(env, ret, bvl, trBody);
      std::shared_ptr<SygusGrammar> bodyG = std::make_shared<SygusGrammar>(std::vector<Node>(), tnbBody);

      // add bodyG to lists so its nonterminals/rules get merged later
      allSubGrammars.push_back(bodyG);
      const std::vector<Node>& bodyNts = bodyG->getNtSyms();
      ntAll.insert(ntAll.end(), bodyNts.begin(), bodyNts.end());

      // now choose the Boolean nonterminal to which we'll attach the FORALL
      Node bodyBoolNt;
      for (const Node& snt : bodyNts)
      {
        if (snt.getType().isBoolean())
        {
          bodyBoolNt = snt;
          Trace("mbqi-enum-quant-grammar") << "...found Boolean nonterminal (body) " << bodyBoolNt << std::endl;
          break;
        }
      }
      Assert(!bodyBoolNt.isNull());

      // construct a simple Boolean body for the FORALL (e.g., (= varNT varNT))
      Assert(!varNTs.empty());
      Node eqTerm = nm->mkNode(Kind::EQUAL, varNTs[0], varNTs[0]);

      Node bvlQ = nm->mkNode(Kind::BOUND_VAR_LIST, qvars);
      Node forallNode = nm->mkNode(Kind::FORALL, bvlQ, eqTerm);

      // add forallNode to the body subgrammar's Boolean nonterminal
      bodyG->addRules(bodyBoolNt, {forallNode});

      Trace("mbqi-enum-quant-grammar")
          << "  attached FORALL node to body-subgrammar Boolean nonterminal " << bodyBoolNt
          << ": " << forallNode << std::endl;

      // store the forall node to attach to the main combined grammar later
      typeToQuantRule[ntt] = forallNode;
    } // end for each function-type nonterminal

    Trace("mbqi-enum-quant-grammar") << "Make combined " << ntAll << std::endl;

    // create combined grammar with all NTs (main + subgrammars)
    SygusGrammar sgcom({}, ntAll);

    // add rules from every subgrammar we created (argument subgrammars + body subgrammars)
    for (const std::shared_ptr<SygusGrammar>& sgptr : allSubGrammars)
    {
      SygusGrammar& sgb = *sgptr;
      const std::vector<Node>& sgbNts = sgb.getNtSyms();
      for (const Node& snt : sgbNts)
      {
        const std::vector<Node>& srules = sgb.getRulesFor(snt);
        if (!srules.empty())
        {
          Trace("mbqi-enum-quant-grammar")
              << "  collect rules from subgram " << snt << " -> " << srules << std::endl;
          sgcom.addRules(snt, srules);
        }
      }
    }

    // add original grammar rules (so main non-terminals are present)
    for (const Node& nt : nts)
    {
      Trace("mbqi-enum-quant-grammar") << "- non-terminal in sgg: " << nt << std::endl;
      std::vector<Node> rules = sgg.getRulesFor(nt);
      sgcom.addRules(nt, rules);
    }

    // attach FORALL nodes (prepending them) to a Boolean nonterminal in the combined grammar
    //    (we attach each function-type's forall to the first Boolean nonterminal we find)
    for (const auto& itFR : typeToQuantRule)
    {
      Node forallNode = itFR.second;
      bool attached = false;
      for (const Node& ntb : sgcom.getNtSyms())
      {
        if (ntb.getType().isBoolean())
        {
          std::vector<Node> rules = sgcom.getRulesFor(ntb);
          Trace("mbqi-enum-quant-grammar")
              << "...add " << forallNode << " to Boolean non-terminal " << ntb << std::endl;
          // prepend forall as the first alternative to try it first
          rules.insert(rules.begin(), forallNode);
          sgcom.addRules(ntb, rules);
          attached = true;
          break;
        }
      }
      if (!attached)
      {
        Trace("mbqi-enum-quant-grammar")
            << "could not attach FORALL " << forallNode << " (no Boolean non-terminal found in combined grammar) " << std::endl;
      }
    }

    // finalize combined grammar
    TypeNode gcom = sgcom.resolve();
    Trace("mbqi-enum-quant-grammar") << "Combined grammar:" << std::endl;
    Trace("mbqi-enum-quant-grammar")
        << printer::smt2::Smt2Printer::sygusGrammarString(gcom) << std::endl;

    tuse = gcom;
    d_senumCb.reset(new MbqiEnumTermEnumeratorCallback(env));
  }
  d_senum.reset(new SygusTermEnumerator(env, tuse, d_senumCb.get()));

  /*
    for (size_t i = 0; i < 5000; i++)
    {
      Node et;
      do
      {
        et = getEnumeratedTerm(nm, i);
      } while (et.isNull());
      Trace("mbqi-enum-debug") << "TMP Enum term: #" << i << " is " << et << std::endl;
      std::vector<std::pair<Node, InferenceId>> lemmas =
    getEnumeratedLemmas(et); for (std::pair<Node, InferenceId>& al : lemmas)
      {
        Trace("mbqi-enum") << "...new lemma: " << al.first << std::endl;
      }
    }
    exit(1);
    */
}

std::vector<std::pair<Node, InferenceId>> MVarInfo::getEnumeratedLemmas(
    const Node& t)
{
  std::vector<std::pair<Node, InferenceId>> lemmas;
  if (d_cenc != nullptr)
  {
    lemmas = d_cenc->getEnumeratedLemmas(t);
  }
  return lemmas;
}

std::vector<std::pair<Node, InferenceId>>
MVarInfo::ChoiceElimNodeConverter::getEnumeratedLemmas(const Node& t)
{
  std::vector<std::pair<Node, InferenceId>> lemmas;
  std::unordered_set<Node> syms;
  expr::getSymbols(t, syms, d_visited);
  Trace("mbqi-enum-debug") << "getEnumeratedLemmas for " << t << std::endl;
  std::map<Node, Node>::iterator itl;
  for (const Node& s : syms)
  {
    Trace("mbqi-enum-debug") << "...is lemma sym " << s << "?" << std::endl;
    itl = d_lemmas.find(s);
    if (itl != d_lemmas.end())
    {
      lemmas.emplace_back(itl->second,
                          InferenceId::QUANTIFIERS_MBQI_ENUM_CHOICE);
    }
  }
  return lemmas;
}

Node MVarInfo::getEnumeratedTerm(NodeManager* nm, size_t i)
{
  size_t nullCount = 0;
  while (i >= d_enum.size())
  {
    Node curr = d_senum->getCurrent();
    Trace("mbqi-enum-debug") << "Enumerate: " << curr << std::endl;
    if (!curr.isNull())
    {
      // use converter if it exists
      if (d_cenc != nullptr)
      {
        curr = d_cenc->convert(curr);
      }
      if (!d_lamVars.isNull())
      {
        curr = nm->mkNode(Kind::LAMBDA, d_lamVars, curr);
      }
      Assert(!curr.isNull());
      d_enum.push_back(curr);
      nullCount = 0;
    }
    else
    {
      nullCount++;
      if (nullCount > 100)
      {
        // break if we aren't making progress
        break;
      }
    }
    if (!d_senum->incrementPartial())
    {
      // enumeration is finished
      break;
    }
  }
  if (i >= d_enum.size())
  {
    Trace("mbqi-enum-debug") << "... return null" << std::endl;
    return Node::null();
  }
  Assert(!d_enum[i].isNull());
  return d_enum[i];
}

void MQuantInfo::initialize(Env& env, InstStrategyMbqi& parent, const Node& q)
{
  // The externally provided terminal rules. This set is shared between
  // all variables we instantiate.
  std::vector<Node> etrules;
  // include the global symbols if applicable
  if (env.getOptions().quantifiers.mbqiEnumGlobalSymGrammar)
  {
    const context::CDHashSet<Node>& gsyms = parent.getGlobalSyms();
    for (const Node& v : gsyms)
    {
      etrules.push_back(v);
    }
  }
  for (const Node& v : q[0])
  {
    size_t index = d_vinfo.size();
    d_vinfo.emplace_back();
    TypeNode vtn = v.getType();
    // if enumerated, add to list
    if (shouldEnumerate(env.getOptions(), vtn))
    {
      d_indices.push_back(index);
    }
    else
    {
      d_nindices.push_back(index);
      // include variables defined in terms of others if applicable
      if (env.getOptions().quantifiers.mbqiEnumExtVarsGrammar)
      {
        etrules.push_back(v);
      }
    }
  }
  // initialize the variables we are instantiating
  for (size_t index : d_indices)
  {
    // start with the shared terminal rules
    std::vector<Node> etrulesLocal = etrules;
    // if (env.getOptions().quantifiers.mbqiEnumFreeSymsGrammar)
    // {
    //   // collect full terms (applications of symbols) if applicable
    //   std::unordered_set<Node> terms;
    //   expr::getTerms(q[1], terms);
    //   for (const Node& t : terms)
    //   {
    //     // skip terms that mention the variable we are instantiating
    //     Node v = q[0][index]; 
    //     if (expr::hasSubterm(t, v))
    //     {
    //       continue;
    //     }
    //     etrulesLocal.push_back(t);
    //   }
    // }
    // initialize the variables we are instantiating
    d_vinfo[index].initialize(env, q, q[0][index], etrulesLocal);
  }
}

MVarInfo& MQuantInfo::getVarInfo(size_t index)
{
  Assert(index < d_vinfo.size());
  return d_vinfo[index];
}

std::vector<size_t> MQuantInfo::getInstIndices() { return d_indices; }
std::vector<size_t> MQuantInfo::getNoInstIndices() { return d_nindices; }

MbqiEnum::MbqiEnum(Env& env, InstStrategyMbqi& parent)
    : EnvObj(env), d_parent(parent)
{
  d_subOptions.copyValues(options());
  d_subOptions.write_quantifiers().instMaxRounds = 5;
  smt::SetDefaults::disableChecking(d_subOptions);
}

MQuantInfo& MbqiEnum::getOrMkQuantInfo(const Node& q)
{
  auto [it, inserted] = d_qinfo.try_emplace(q);
  if (inserted)
  {
    it->second.initialize(d_env, d_parent, q);
  }
  return it->second;
}

bool MbqiEnum::constructInstantiation(
    const Node& q,
    const Node& query,
    const std::vector<Node>& vars,
    std::vector<Node>& mvs,
    const std::map<Node, Node>& mvFreshVar,
    std::vector<std::pair<Node, InferenceId>>& auxLemmas)
{
  Assert(q[0].getNumChildren() == vars.size());
  Assert(vars.size() == mvs.size());
  if (TraceIsOn("mbqi-enum"))
  {
    Trace("mbqi-enum") << "Instantiate " << q << std::endl;
    for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
    {
      Trace("mbqi-enum")
          << "  " << q[0][i] << " -> " << mvs[i] << std::endl;
    }
  }
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  MQuantInfo& qi = getOrMkQuantInfo(q);
  std::vector<size_t> indices = qi.getInstIndices();
  std::vector<size_t> nindices = qi.getNoInstIndices();
  Subs inst;
  Subs vinst;
  std::unordered_map<Node, Node> tmpCMap;
  for (size_t i : nindices)
  {
    Node v = mvs[i];
    v = d_parent.convertFromModel(v, tmpCMap, mvFreshVar);
    if (v.isNull())
    {
      Trace("mbqi-enum-model") << "Failed to convert " << v << std::endl;
      return false;
    }
    Trace("mbqi-enum-model")
        << "* Assume: " << q[0][i] << " -> " << v << std::endl;
    // if we don't enumerate it, we are already considering this instantiation
    inst.add(vars[i], v);
    vinst.add(q[0][i], v);
  }
  Node queryCurr = query;
  Trace("mbqi-enum-model") << "...query is " << queryCurr << std::endl;
  queryCurr = rewrite(inst.apply(queryCurr));
  Trace("mbqi-enum-model")
      << "...processed is " << queryCurr << std::endl;
  // consider variables in random order, for diversity of instantiations
  std::shuffle(indices.begin(), indices.end(), Random::getRandom());
  bool addedInst = false;
  for (size_t i = 0, isize = indices.size(); i < isize; i++)
  {
    size_t ii = indices[i];
    TNode v = vars[ii];
    MVarInfo& vi = qi.getVarInfo(ii);
    size_t cindex = 0;
    bool success = false;
    bool successEnum;
    bool lastVar = (i + 1 == isize);
    do
    {
      Node ret = vi.getEnumeratedTerm(nodeManager(), cindex);
      cindex++;
      Node retc;
      if (!ret.isNull())
      {
        Trace("mbqi-enum-debug") << "TMP - Try candidate: " << q.getId() << " " << v
                          << " " << cindex << " " << ret << std::endl;
        Trace("mbqi-enum") << "- Try candidate: " << ret << std::endl;
        // apply current substitution (to account for cases where ret has
        // other variables in its grammar).
        ret = vinst.apply(ret);
        retc = ret;
        successEnum = true;
        // now convert the value
        std::unordered_map<Node, Node> tmpConvertMap;
        std::map<TypeNode, std::unordered_set<Node> > freshVarType;
        retc = d_parent.convertToQuery(retc, tmpConvertMap, freshVarType);
      }
      else
      {
        Trace("mbqi-enum-debug")
            << "- Failed to enumerate candidate" << std::endl;
        // if we failed to enumerate, just try the original
        Node mc = d_parent.convertFromModel(mvs[ii], tmpCMap, mvFreshVar);
        if (mc.isNull())
        {
          Trace("mbqi-enum-debug") << "Failed to convert " << mvs[ii] << std::endl;
          // if failed to convert, we fail
          return false;
        }
        ret = mc;
        retc = mc;
        successEnum = false;
      }
      Trace("mbqi-enum-model")
          << "- Converted candidate: " << v << " -> " << retc << std::endl;
      Node queryCheck;
      // see if it is still satisfiable, if still SAT, we replace
      queryCheck = queryCurr.substitute(v, TNode(retc));
      queryCheck = rewrite(queryCheck);
      Trace("mbqi-enum-model")
          << "...check " << queryCheck << std::endl;
      // Result r = checkWithSubsolver(queryCheck, ssi);
      Result r = d_parent.checkWithSubsolverSimple(queryCheck, ssi);
      success = (r != Result::UNSAT);
      if (success)
      {
        // remember the updated query
        queryCurr = queryCheck;
        Trace("mbqi-enum-model") << "...success" << std::endl;
        Trace("mbqi-enum")
            << "* Enumerated " << q[0][ii] << " -> " << ret << std::endl;
        mvs[ii] = ret;
        vinst.add(q[0][ii], ret);
      }
      // We verify the lemma is successfully added here. If it is not, then
      // success is false and we continue the enumeration.
      if (lastVar && success)
      {
        success = d_parent.tryInstantiation(
            q, mvs, InferenceId::QUANTIFIERS_INST_MBQI_ENUM, mvFreshVar);
        addedInst = addedInst || success;
      }

      if (!success && !successEnum)
      {
        // we did not enumerate a candidate, and tried the original, which
        // failed.
        Trace("mbqi-enum-debug") << "Failed to enumerate" << std::endl;
        return false;
      }
    } while (!success);
  }
  // See if there are auxiliary lemmas, if so, add them to the returned
  // vector.
  Trace("mbqi-enum-debug") << "Instantiate: " << q.getId() << std::endl;
  for (size_t i = 0, isize = indices.size(); i < isize; i++)
  {
    size_t ii = indices[i];
    TNode v = vars[ii];
    Trace("mbqi-enum-debug") << "- " << v << " -> " << mvs[ii] << std::endl;
    MVarInfo& vi = qi.getVarInfo(ii);
    std::vector<std::pair<Node, InferenceId>> alv =
        vi.getEnumeratedLemmas(mvs[ii]);
    Trace("mbqi-enum-debug") << "..." << alv.size() << " aux lemmas" << std::endl;
    auxLemmas.insert(auxLemmas.end(), alv.begin(), alv.end());
  }
  return addedInst;
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
