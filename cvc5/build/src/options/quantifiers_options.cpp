/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Option template for option modules.
 *
 * For each <module>_options.toml configuration file, mkoptions.py
 * expands this template and generates a <module>_options.cpp file.
 */
#include "options/quantifiers_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, QcfMode mode)
{
  switch(mode)
  {
    case QcfMode::CONFLICT_ONLY: return os << "conflict";
    case QcfMode::PROP_EQ: return os << "prop-eq";
    default: Unreachable();
  }
  return os;
}
QcfMode stringToQcfMode(const std::string& optarg)
{
  if (optarg == "conflict") return QcfMode::CONFLICT_ONLY;
  else if (optarg == "prop-eq") return QcfMode::PROP_EQ;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Quantifier conflict find modes.
Available modes for --cbqi-mode are:
+ conflict
  Apply QCF algorithm to find conflicts only.
+ prop-eq (default)
  Apply QCF algorithm to propagate equalities as well as conflicts.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --cbqi-mode: `") +
                        optarg + "'.  Try --cbqi-mode=help.");
}
std::ostream& operator<<(std::ostream& os, CegisSampleMode mode)
{
  switch(mode)
  {
    case CegisSampleMode::NONE: return os << "none";
    case CegisSampleMode::USE: return os << "use";
    case CegisSampleMode::TRUST: return os << "trust";
    default: Unreachable();
  }
  return os;
}
CegisSampleMode stringToCegisSampleMode(const std::string& optarg)
{
  if (optarg == "none") return CegisSampleMode::NONE;
  else if (optarg == "use") return CegisSampleMode::USE;
  else if (optarg == "trust") return CegisSampleMode::TRUST;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for sampling with counterexample-guided inductive synthesis (CEGIS).
Available modes for --cegis-sample are:
+ none (default)
  Do not use sampling with CEGIS.
+ use
  Use sampling to accelerate CEGIS. This will rule out solutions for a
  conjecture when they are not satisfied by a sample point.
+ trust
  Trust that when a solution for a conjecture is always true under sampling,
  then it is indeed a solution. Note this option may print out spurious
  solutions for synthesis conjectures.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --cegis-sample: `") +
                        optarg + "'.  Try --cegis-sample=help.");
}
std::ostream& operator<<(std::ostream& os, CegqiBvIneqMode mode)
{
  switch(mode)
  {
    case CegqiBvIneqMode::EQ_SLACK: return os << "eq-slack";
    case CegqiBvIneqMode::EQ_BOUNDARY: return os << "eq-boundary";
    case CegqiBvIneqMode::KEEP: return os << "keep";
    default: Unreachable();
  }
  return os;
}
CegqiBvIneqMode stringToCegqiBvIneqMode(const std::string& optarg)
{
  if (optarg == "eq-slack") return CegqiBvIneqMode::EQ_SLACK;
  else if (optarg == "eq-boundary") return CegqiBvIneqMode::EQ_BOUNDARY;
  else if (optarg == "keep") return CegqiBvIneqMode::KEEP;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for handling bit-vector inequalities in counterexample-guided
  instantiation.
Available modes for --cegqi-bv-ineq are:
+ eq-slack
  Solve for the inequality using the slack value in the model, e.g., t > s
  becomes t = s + ( t-s )^M.
+ eq-boundary (default)
  Solve for the boundary point of the inequality, e.g., t > s becomes t = s+1.
+ keep
  Solve for the inequality directly using side conditions for invertibility.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --cegqi-bv-ineq: `") +
                        optarg + "'.  Try --cegqi-bv-ineq=help.");
}
std::ostream& operator<<(std::ostream& os, CondVarSplitQuantMode mode)
{
  switch(mode)
  {
    case CondVarSplitQuantMode::OFF: return os << "off";
    case CondVarSplitQuantMode::ON: return os << "on";
    case CondVarSplitQuantMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
CondVarSplitQuantMode stringToCondVarSplitQuantMode(const std::string& optarg)
{
  if (optarg == "off") return CondVarSplitQuantMode::OFF;
  else if (optarg == "on") return CondVarSplitQuantMode::ON;
  else if (optarg == "agg") return CondVarSplitQuantMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for splitting quantified formulas that lead to variable eliminations.
Available modes for --cond-var-split-quant are:
+ off
  Do not split quantified formulas.
+ on (default)
  Split quantified formulas that lead to variable eliminations.
+ agg
  Aggressively split quantified formulas that lead to variable eliminations.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --cond-var-split-quant: `") +
                        optarg + "'.  Try --cond-var-split-quant=help.");
}
std::ostream& operator<<(std::ostream& os, FmfMbqiMode mode)
{
  switch(mode)
  {
    case FmfMbqiMode::NONE: return os << "none";
    case FmfMbqiMode::FMC: return os << "fmc";
    case FmfMbqiMode::TRUST: return os << "trust";
    default: Unreachable();
  }
  return os;
}
FmfMbqiMode stringToFmfMbqiMode(const std::string& optarg)
{
  if (optarg == "none") return FmfMbqiMode::NONE;
  else if (optarg == "fmc") return FmfMbqiMode::FMC;
  else if (optarg == "trust") return FmfMbqiMode::TRUST;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Model-based quantifier instantiation modes.
Available modes for --fmf-mbqi are:
+ none
  Disable model-based quantifier instantiation.
+ fmc (default)
  Use algorithm from Section 5.4.2 of thesis Finite Model Finding in
  Satisfiability Modulo Theories.
+ trust
  Do not instantiate quantified formulas (incomplete technique).
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --fmf-mbqi: `") +
                        optarg + "'.  Try --fmf-mbqi=help.");
}
std::ostream& operator<<(std::ostream& os, IevalMode mode)
{
  switch(mode)
  {
    case IevalMode::OFF: return os << "off";
    case IevalMode::USE: return os << "use";
    case IevalMode::USE_LEARN: return os << "use-learn";
    default: Unreachable();
  }
  return os;
}
IevalMode stringToIevalMode(const std::string& optarg)
{
  if (optarg == "off") return IevalMode::OFF;
  else if (optarg == "use") return IevalMode::USE;
  else if (optarg == "use-learn") return IevalMode::USE_LEARN;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Mode for using instantiation evaluation.
Available modes for --ieval are:
+ off (default)
  Do not use instantiation evaluation.
+ use
  Use instantiation evaluation.
+ use-learn
  Use instantiation evaluation, and generalize learning.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --ieval: `") +
                        optarg + "'.  Try --ieval=help.");
}
std::ostream& operator<<(std::ostream& os, InstWhenMode mode)
{
  switch(mode)
  {
    case InstWhenMode::FULL: return os << "full";
    case InstWhenMode::FULL_DELAY: return os << "full-delay";
    case InstWhenMode::FULL_LAST_CALL: return os << "full-last-call";
    case InstWhenMode::FULL_DELAY_LAST_CALL: return os << "full-delay-last-call";
    case InstWhenMode::LAST_CALL: return os << "last-call";
    default: Unreachable();
  }
  return os;
}
InstWhenMode stringToInstWhenMode(const std::string& optarg)
{
  if (optarg == "full") return InstWhenMode::FULL;
  else if (optarg == "full-delay") return InstWhenMode::FULL_DELAY;
  else if (optarg == "full-last-call") return InstWhenMode::FULL_LAST_CALL;
  else if (optarg == "full-delay-last-call") return InstWhenMode::FULL_DELAY_LAST_CALL;
  else if (optarg == "last-call") return InstWhenMode::LAST_CALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Instantiation modes.
Available modes for --inst-when are:
+ full
  Run instantiation round at full effort, before theory combination.
+ full-delay
  Run instantiation round at full effort, before theory combination, after all
  other theories have finished.
+ full-last-call (default)
  Alternate running instantiation rounds at full effort and last call.  In other
  words, interleave instantiation and theory combination.
+ full-delay-last-call
  Alternate running instantiation rounds at full effort after all other theories
  have finished, and last call.
+ last-call
  Run instantiation at last call effort, after theory combination and and
  theories report sat.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --inst-when: `") +
                        optarg + "'.  Try --inst-when=help.");
}
std::ostream& operator<<(std::ostream& os, IteLiftQuantMode mode)
{
  switch(mode)
  {
    case IteLiftQuantMode::NONE: return os << "none";
    case IteLiftQuantMode::SIMPLE: return os << "simple";
    case IteLiftQuantMode::ALL: return os << "all";
    default: Unreachable();
  }
  return os;
}
IteLiftQuantMode stringToIteLiftQuantMode(const std::string& optarg)
{
  if (optarg == "none") return IteLiftQuantMode::NONE;
  else if (optarg == "simple") return IteLiftQuantMode::SIMPLE;
  else if (optarg == "all") return IteLiftQuantMode::ALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  ITE lifting modes for quantified formulas.
Available modes for --ite-lift-quant are:
+ none
  Do not lift if-then-else in quantified formulas.
+ simple (default)
  Lift if-then-else in quantified formulas if results in smaller term size.
+ all
  Lift if-then-else in quantified formulas.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --ite-lift-quant: `") +
                        optarg + "'.  Try --ite-lift-quant=help.");
}
std::ostream& operator<<(std::ostream& os, LiteralMatchMode mode)
{
  switch(mode)
  {
    case LiteralMatchMode::NONE: return os << "none";
    case LiteralMatchMode::USE: return os << "use";
    case LiteralMatchMode::AGG_PREDICATE: return os << "agg-predicate";
    case LiteralMatchMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
LiteralMatchMode stringToLiteralMatchMode(const std::string& optarg)
{
  if (optarg == "none") return LiteralMatchMode::NONE;
  else if (optarg == "use") return LiteralMatchMode::USE;
  else if (optarg == "agg-predicate") return LiteralMatchMode::AGG_PREDICATE;
  else if (optarg == "agg") return LiteralMatchMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Literal match modes.
Available modes for --literal-matching are:
+ none
  Do not use literal matching.
+ use (default)
  Consider phase requirements of triggers conservatively. For example, the
  trigger P( x ) in forall( x ). ( P( x ) V ~Q( x ) ) will not be matched with
  terms in the equivalence class of true, and likewise Q( x ) will not be
  matched terms in the equivalence class of false. Extends to equality.
+ agg-predicate
  Consider phase requirements aggressively for predicates. In the above example,
  only match P( x ) with terms that are in the equivalence class of false.
+ agg
  Consider the phase requirements aggressively for all triggers.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --literal-matching: `") +
                        optarg + "'.  Try --literal-matching=help.");
}
std::ostream& operator<<(std::ostream& os, MacrosQuantMode mode)
{
  switch(mode)
  {
    case MacrosQuantMode::ALL: return os << "all";
    case MacrosQuantMode::GROUND: return os << "ground";
    case MacrosQuantMode::GROUND_UF: return os << "ground-uf";
    default: Unreachable();
  }
  return os;
}
MacrosQuantMode stringToMacrosQuantMode(const std::string& optarg)
{
  if (optarg == "all") return MacrosQuantMode::ALL;
  else if (optarg == "ground") return MacrosQuantMode::GROUND;
  else if (optarg == "ground-uf") return MacrosQuantMode::GROUND_UF;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for quantifiers macro expansion.
Available modes for --macros-quant-mode are:
+ all
  Infer definitions for functions, including those containing quantified
  formulas.
+ ground
  Only infer ground definitions for functions.
+ ground-uf (default)
  Only infer ground definitions for functions that result in triggers for all
  free variables.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --macros-quant-mode: `") +
                        optarg + "'.  Try --macros-quant-mode=help.");
}
std::ostream& operator<<(std::ostream& os, MiniscopeQuantMode mode)
{
  switch(mode)
  {
    case MiniscopeQuantMode::OFF: return os << "off";
    case MiniscopeQuantMode::CONJ: return os << "conj";
    case MiniscopeQuantMode::FV: return os << "fv";
    case MiniscopeQuantMode::CONJ_AND_FV: return os << "conj-and-fv";
    case MiniscopeQuantMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
MiniscopeQuantMode stringToMiniscopeQuantMode(const std::string& optarg)
{
  if (optarg == "off") return MiniscopeQuantMode::OFF;
  else if (optarg == "conj") return MiniscopeQuantMode::CONJ;
  else if (optarg == "fv") return MiniscopeQuantMode::FV;
  else if (optarg == "conj-and-fv") return MiniscopeQuantMode::CONJ_AND_FV;
  else if (optarg == "agg") return MiniscopeQuantMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Miniscope quantifiers modes.
Available modes for --miniscope-quant are:
+ off
  Do not miniscope quantifiers.
+ conj
  Use miniscoping of conjunctions only.
+ fv
  Use free variable miniscoping only.
+ conj-and-fv (default)
  Enable both conjunction and free variable miniscoping.
+ agg
  Enable aggressive miniscope, which further may rewrite quantified formulas
  into a form where miniscoping is possible.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --miniscope-quant: `") +
                        optarg + "'.  Try --miniscope-quant=help.");
}
std::ostream& operator<<(std::ostream& os, PreSkolemQuantMode mode)
{
  switch(mode)
  {
    case PreSkolemQuantMode::OFF: return os << "off";
    case PreSkolemQuantMode::ON: return os << "on";
    case PreSkolemQuantMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
PreSkolemQuantMode stringToPreSkolemQuantMode(const std::string& optarg)
{
  if (optarg == "off") return PreSkolemQuantMode::OFF;
  else if (optarg == "on") return PreSkolemQuantMode::ON;
  else if (optarg == "agg") return PreSkolemQuantMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes to apply skolemization eagerly to bodies of quantified formulas.
Available modes for --pre-skolem-quant are:
+ off (default)
  Do not apply Skolemization eagerly.
+ on
  Apply Skolemization eagerly to top-level (negatively asserted) quantified
  formulas.
+ agg
  Apply Skolemization eagerly and aggressively during preprocessing.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --pre-skolem-quant: `") +
                        optarg + "'.  Try --pre-skolem-quant=help.");
}
std::ostream& operator<<(std::ostream& os, PrenexQuantMode mode)
{
  switch(mode)
  {
    case PrenexQuantMode::NONE: return os << "none";
    case PrenexQuantMode::SIMPLE: return os << "simple";
    case PrenexQuantMode::NORMAL: return os << "norm";
    default: Unreachable();
  }
  return os;
}
PrenexQuantMode stringToPrenexQuantMode(const std::string& optarg)
{
  if (optarg == "none") return PrenexQuantMode::NONE;
  else if (optarg == "simple") return PrenexQuantMode::SIMPLE;
  else if (optarg == "norm") return PrenexQuantMode::NORMAL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Prenex quantifiers modes.
Available modes for --prenex-quant are:
+ none
  Do not prenex nested quantifiers.
+ simple (default)
  Do simple prenexing of same sign quantifiers.
+ norm
  Prenex to prenex normal form.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --prenex-quant: `") +
                        optarg + "'.  Try --prenex-quant=help.");
}
std::ostream& operator<<(std::ostream& os, PrintInstMode mode)
{
  switch(mode)
  {
    case PrintInstMode::LIST: return os << "list";
    case PrintInstMode::NUM: return os << "num";
    default: Unreachable();
  }
  return os;
}
PrintInstMode stringToPrintInstMode(const std::string& optarg)
{
  if (optarg == "list") return PrintInstMode::LIST;
  else if (optarg == "num") return PrintInstMode::NUM;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Print format for printing instantiations.
Available modes for --print-inst are:
+ list (default)
  Print the list of instantiations per quantified formula, when non-empty.
+ num
  Print the total number of instantiations per quantified formula, when
  non-zero.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --print-inst: `") +
                        optarg + "'.  Try --print-inst=help.");
}
std::ostream& operator<<(std::ostream& os, QuantDSplitMode mode)
{
  switch(mode)
  {
    case QuantDSplitMode::NONE: return os << "none";
    case QuantDSplitMode::DEFAULT: return os << "default";
    case QuantDSplitMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
QuantDSplitMode stringToQuantDSplitMode(const std::string& optarg)
{
  if (optarg == "none") return QuantDSplitMode::NONE;
  else if (optarg == "default") return QuantDSplitMode::DEFAULT;
  else if (optarg == "agg") return QuantDSplitMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for quantifiers splitting.
Available modes for --quant-dsplit are:
+ none
  Never split quantified formulas.
+ default
  Split quantified formulas over some finite datatypes when finite model finding
  is enabled.
+ agg
  Aggressively split quantified formulas.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --quant-dsplit: `") +
                        optarg + "'.  Try --quant-dsplit=help.");
}
std::ostream& operator<<(std::ostream& os, QuantRepMode mode)
{
  switch(mode)
  {
    case QuantRepMode::EE: return os << "ee";
    case QuantRepMode::FIRST: return os << "first";
    case QuantRepMode::DEPTH: return os << "depth";
    default: Unreachable();
  }
  return os;
}
QuantRepMode stringToQuantRepMode(const std::string& optarg)
{
  if (optarg == "ee") return QuantRepMode::EE;
  else if (optarg == "first") return QuantRepMode::FIRST;
  else if (optarg == "depth") return QuantRepMode::DEPTH;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for quantifiers representative selection.
Available modes for --quant-rep-mode are:
+ ee
  Let equality engine choose representatives.
+ first (default)
  Choose terms that appear first.
+ depth
  Choose terms that are of minimal depth.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --quant-rep-mode: `") +
                        optarg + "'.  Try --quant-rep-mode=help.");
}
std::ostream& operator<<(std::ostream& os, SygusEnumMode mode)
{
  switch(mode)
  {
    case SygusEnumMode::SMART: return os << "smart";
    case SygusEnumMode::FAST: return os << "fast";
    case SygusEnumMode::RANDOM: return os << "random";
    case SygusEnumMode::VAR_AGNOSTIC: return os << "var-agnostic";
    case SygusEnumMode::AUTO: return os << "auto";
    default: Unreachable();
  }
  return os;
}
SygusEnumMode stringToSygusEnumMode(const std::string& optarg)
{
  if (optarg == "smart") return SygusEnumMode::SMART;
  else if (optarg == "fast") return SygusEnumMode::FAST;
  else if (optarg == "random") return SygusEnumMode::RANDOM;
  else if (optarg == "var-agnostic") return SygusEnumMode::VAR_AGNOSTIC;
  else if (optarg == "auto") return SygusEnumMode::AUTO;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for sygus enumeration.
Available modes for --sygus-enum are:
+ smart
  Use smart enumeration based on datatype constraints.
+ fast
  Use optimized enumerator for sygus enumeration.
+ random
  Use basic random enumerator for sygus enumeration.
+ var-agnostic
  Use sygus solver to enumerate terms that are agnostic to variables.
+ auto (default)
  Internally decide the best policy for each enumerator.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-enum: `") +
                        optarg + "'.  Try --sygus-enum=help.");
}
std::ostream& operator<<(std::ostream& os, SygusEvalUnfoldMode mode)
{
  switch(mode)
  {
    case SygusEvalUnfoldMode::NONE: return os << "none";
    case SygusEvalUnfoldMode::SINGLE: return os << "single";
    case SygusEvalUnfoldMode::SINGLE_BOOL: return os << "single-bool";
    case SygusEvalUnfoldMode::MULTI: return os << "multi";
    default: Unreachable();
  }
  return os;
}
SygusEvalUnfoldMode stringToSygusEvalUnfoldMode(const std::string& optarg)
{
  if (optarg == "none") return SygusEvalUnfoldMode::NONE;
  else if (optarg == "single") return SygusEvalUnfoldMode::SINGLE;
  else if (optarg == "single-bool") return SygusEvalUnfoldMode::SINGLE_BOOL;
  else if (optarg == "multi") return SygusEvalUnfoldMode::MULTI;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for sygus evaluation unfolding.
Available modes for --sygus-eval-unfold are:
+ none
  Do not use sygus evaluation unfolding.
+ single
  Do single-step unfolding for all evaluation functions.
+ single-bool (default)
  Do single-step unfolding for Boolean functions and ITEs, and multi-step
  unfolding for all others.
+ multi
  Do multi-step unfolding for all evaluation functions.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-eval-unfold: `") +
                        optarg + "'.  Try --sygus-eval-unfold=help.");
}
std::ostream& operator<<(std::ostream& os, SygusFilterSolMode mode)
{
  switch(mode)
  {
    case SygusFilterSolMode::NONE: return os << "none";
    case SygusFilterSolMode::STRONG: return os << "strong";
    case SygusFilterSolMode::WEAK: return os << "weak";
    default: Unreachable();
  }
  return os;
}
SygusFilterSolMode stringToSygusFilterSolMode(const std::string& optarg)
{
  if (optarg == "none") return SygusFilterSolMode::NONE;
  else if (optarg == "strong") return SygusFilterSolMode::STRONG;
  else if (optarg == "weak") return SygusFilterSolMode::WEAK;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for filtering sygus solutions.
Available modes for --sygus-filter-sol are:
+ none (default)
  Do not filter sygus solutions.
+ strong
  Filter solutions that are logically stronger than others.
+ weak
  Filter solutions that are logically weaker than others.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-filter-sol: `") +
                        optarg + "'.  Try --sygus-filter-sol=help.");
}
std::ostream& operator<<(std::ostream& os, SygusGrammarConsMode mode)
{
  switch(mode)
  {
    case SygusGrammarConsMode::SIMPLE: return os << "simple";
    case SygusGrammarConsMode::ANY_CONST: return os << "any-const";
    case SygusGrammarConsMode::ANY_TERM: return os << "any-term";
    case SygusGrammarConsMode::ANY_TERM_CONCISE: return os << "any-term-concise";
    default: Unreachable();
  }
  return os;
}
SygusGrammarConsMode stringToSygusGrammarConsMode(const std::string& optarg)
{
  if (optarg == "simple") return SygusGrammarConsMode::SIMPLE;
  else if (optarg == "any-const") return SygusGrammarConsMode::ANY_CONST;
  else if (optarg == "any-term") return SygusGrammarConsMode::ANY_TERM;
  else if (optarg == "any-term-concise") return SygusGrammarConsMode::ANY_TERM_CONCISE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for default SyGuS grammars.
Available modes for --sygus-grammar-cons are:
+ simple (default)
  Use simple grammar construction (no symbolic terms or constants).
+ any-const
  Use symoblic constant constructors.
+ any-term
  When applicable, use constructors corresponding to any symbolic term. This
  option enables a sum-of-monomials grammar for arithmetic. For all other types,
  it enables symbolic constant constructors.
+ any-term-concise
  When applicable, use constructors corresponding to any symbolic term, favoring
  conciseness over generality. This option is equivalent to any-term but enables
  a polynomial grammar for arithmetic when not in a combined theory.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-grammar-cons: `") +
                        optarg + "'.  Try --sygus-grammar-cons=help.");
}
std::ostream& operator<<(std::ostream& os, SygusInstMode mode)
{
  switch(mode)
  {
    case SygusInstMode::PRIORITY_INST: return os << "priority-inst";
    case SygusInstMode::PRIORITY_EVAL: return os << "priority-eval";
    case SygusInstMode::INTERLEAVE: return os << "interleave";
    default: Unreachable();
  }
  return os;
}
SygusInstMode stringToSygusInstMode(const std::string& optarg)
{
  if (optarg == "priority-inst") return SygusInstMode::PRIORITY_INST;
  else if (optarg == "priority-eval") return SygusInstMode::PRIORITY_EVAL;
  else if (optarg == "interleave") return SygusInstMode::INTERLEAVE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  SyGuS instantiation lemma modes.
Available modes for --sygus-inst-mode are:
+ priority-inst (default)
  add instantiation lemmas first, add evaluation unfolding if instantiation
  fails.
+ priority-eval
  add evaluation unfolding lemma first, add instantiation lemma if unfolding
  lemmas already added.
+ interleave
  add instantiation and evaluation unfolding lemmas in the same step.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-inst-mode: `") +
                        optarg + "'.  Try --sygus-inst-mode=help.");
}
std::ostream& operator<<(std::ostream& os, SygusInstScope mode)
{
  switch(mode)
  {
    case SygusInstScope::IN: return os << "in";
    case SygusInstScope::OUT: return os << "out";
    case SygusInstScope::BOTH: return os << "both";
    default: Unreachable();
  }
  return os;
}
SygusInstScope stringToSygusInstScope(const std::string& optarg)
{
  if (optarg == "in") return SygusInstScope::IN;
  else if (optarg == "out") return SygusInstScope::OUT;
  else if (optarg == "both") return SygusInstScope::BOTH;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  scope for collecting ground terms for the grammar.
Available modes for --sygus-inst-scope are:
+ in (default)
  use ground terms inside given quantified formula only.
+ out
  use ground terms outside of quantified formulas only.
+ both
  combines inside and outside.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-inst-scope: `") +
                        optarg + "'.  Try --sygus-inst-scope=help.");
}
std::ostream& operator<<(std::ostream& os, SygusInstTermSelMode mode)
{
  switch(mode)
  {
    case SygusInstTermSelMode::MIN: return os << "min";
    case SygusInstTermSelMode::MAX: return os << "max";
    case SygusInstTermSelMode::BOTH: return os << "both";
    default: Unreachable();
  }
  return os;
}
SygusInstTermSelMode stringToSygusInstTermSelMode(const std::string& optarg)
{
  if (optarg == "min") return SygusInstTermSelMode::MIN;
  else if (optarg == "max") return SygusInstTermSelMode::MAX;
  else if (optarg == "both") return SygusInstTermSelMode::BOTH;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Ground term selection modes.
Available modes for --sygus-inst-term-sel are:
+ min (default)
  collect minimal ground terms only.
+ max
  collect maximal ground terms only.
+ both
  combines minimal and maximal .
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-inst-term-sel: `") +
                        optarg + "'.  Try --sygus-inst-term-sel=help.");
}
std::ostream& operator<<(std::ostream& os, SygusInvTemplMode mode)
{
  switch(mode)
  {
    case SygusInvTemplMode::NONE: return os << "none";
    case SygusInvTemplMode::PRE: return os << "pre";
    case SygusInvTemplMode::POST: return os << "post";
    default: Unreachable();
  }
  return os;
}
SygusInvTemplMode stringToSygusInvTemplMode(const std::string& optarg)
{
  if (optarg == "none") return SygusInvTemplMode::NONE;
  else if (optarg == "pre") return SygusInvTemplMode::PRE;
  else if (optarg == "post") return SygusInvTemplMode::POST;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Template modes for sygus invariant synthesis.
Available modes for --sygus-inv-templ are:
+ none
  Synthesize invariant directly.
+ pre
  Synthesize invariant based on weakening of precondition.
+ post (default)
  Synthesize invariant based on strengthening of postcondition.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-inv-templ: `") +
                        optarg + "'.  Try --sygus-inv-templ=help.");
}
std::ostream& operator<<(std::ostream& os, SygusSolutionOutMode mode)
{
  switch(mode)
  {
    case SygusSolutionOutMode::STATUS: return os << "status";
    case SygusSolutionOutMode::STATUS_AND_DEF: return os << "status-and-def";
    case SygusSolutionOutMode::STANDARD: return os << "sygus-standard";
    default: Unreachable();
  }
  return os;
}
SygusSolutionOutMode stringToSygusSolutionOutMode(const std::string& optarg)
{
  if (optarg == "status") return SygusSolutionOutMode::STATUS;
  else if (optarg == "status-and-def") return SygusSolutionOutMode::STATUS_AND_DEF;
  else if (optarg == "sygus-standard") return SygusSolutionOutMode::STANDARD;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for sygus solution output.
Available modes for --sygus-out are:
+ status
  Print only status for check-synth calls.
+ status-and-def
  Print status followed by definition corresponding to solution.
+ sygus-standard (default)
  Print based on SyGuS standard.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-out: `") +
                        optarg + "'.  Try --sygus-out=help.");
}
std::ostream& operator<<(std::ostream& os, SygusQueryGenMode mode)
{
  switch(mode)
  {
    case SygusQueryGenMode::NONE: return os << "none";
    case SygusQueryGenMode::BASIC: return os << "basic";
    case SygusQueryGenMode::SAMPLE_SAT: return os << "sample-sat";
    case SygusQueryGenMode::UNSAT: return os << "unsat";
    default: Unreachable();
  }
  return os;
}
SygusQueryGenMode stringToSygusQueryGenMode(const std::string& optarg)
{
  if (optarg == "none") return SygusQueryGenMode::NONE;
  else if (optarg == "basic") return SygusQueryGenMode::BASIC;
  else if (optarg == "sample-sat") return SygusQueryGenMode::SAMPLE_SAT;
  else if (optarg == "unsat") return SygusQueryGenMode::UNSAT;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for generating interesting satisfiability queries using SyGuS.
Available modes for --sygus-query-gen are:
+ none (default)
  Do not generate queries with SyGuS.
+ basic
  Generate all queries using SyGuS enumeration of the given grammar
+ sample-sat
  Generate interesting SAT queries based on sampling, for e.g. soundness
  testing.
+ unsat
  Generate interesting UNSAT queries, for e.g. proof testing.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-query-gen: `") +
                        optarg + "'.  Try --sygus-query-gen=help.");
}
std::ostream& operator<<(std::ostream& os, SygusQueryDumpFilesMode mode)
{
  switch(mode)
  {
    case SygusQueryDumpFilesMode::NONE: return os << "none";
    case SygusQueryDumpFilesMode::ALL: return os << "all";
    case SygusQueryDumpFilesMode::UNSOLVED: return os << "unsolved";
    default: Unreachable();
  }
  return os;
}
SygusQueryDumpFilesMode stringToSygusQueryDumpFilesMode(const std::string& optarg)
{
  if (optarg == "none") return SygusQueryDumpFilesMode::NONE;
  else if (optarg == "all") return SygusQueryDumpFilesMode::ALL;
  else if (optarg == "unsolved") return SygusQueryDumpFilesMode::UNSOLVED;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Query file options.
Available modes for --sygus-query-gen-dump-files are:
+ none (default)
  Do not dump query files when using --sygus-query-gen.
+ all
  Dump all query files.
+ unsolved
  Dump query files that the subsolver did not solve.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-query-gen-dump-files: `") +
                        optarg + "'.  Try --sygus-query-gen-dump-files=help.");
}
std::ostream& operator<<(std::ostream& os, CegqiSingleInvMode mode)
{
  switch(mode)
  {
    case CegqiSingleInvMode::NONE: return os << "none";
    case CegqiSingleInvMode::USE: return os << "use";
    case CegqiSingleInvMode::ALL: return os << "all";
    default: Unreachable();
  }
  return os;
}
CegqiSingleInvMode stringToCegqiSingleInvMode(const std::string& optarg)
{
  if (optarg == "none") return CegqiSingleInvMode::NONE;
  else if (optarg == "use") return CegqiSingleInvMode::USE;
  else if (optarg == "all") return CegqiSingleInvMode::ALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for single invocation techniques.
Available modes for --sygus-si are:
+ none (default)
  Do not use single invocation techniques.
+ use
  Use single invocation techniques only if grammar is not restrictive.
+ all
  Always use single invocation techniques.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-si: `") +
                        optarg + "'.  Try --sygus-si=help.");
}
std::ostream& operator<<(std::ostream& os, CegqiSingleInvRconsMode mode)
{
  switch(mode)
  {
    case CegqiSingleInvRconsMode::NONE: return os << "none";
    case CegqiSingleInvRconsMode::TRY: return os << "try";
    case CegqiSingleInvRconsMode::ALL_LIMIT: return os << "all-limit";
    case CegqiSingleInvRconsMode::ALL: return os << "all";
    default: Unreachable();
  }
  return os;
}
CegqiSingleInvRconsMode stringToCegqiSingleInvRconsMode(const std::string& optarg)
{
  if (optarg == "none") return CegqiSingleInvRconsMode::NONE;
  else if (optarg == "try") return CegqiSingleInvRconsMode::TRY;
  else if (optarg == "all-limit") return CegqiSingleInvRconsMode::ALL_LIMIT;
  else if (optarg == "all") return CegqiSingleInvRconsMode::ALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for reconstruction solutions while using single invocation techniques.
Available modes for --sygus-si-rcons are:
+ none
  Do not try to reconstruct solutions in the original (user-provided) grammar
  when using single invocation techniques. In this mode, solutions produced by
  cvc5 may violate grammar restrictions.
+ try
  Try to reconstruct solutions in the original grammar when using single
  invocation techniques in an incomplete (fail-fast) manner.
+ all-limit
  Try to reconstruct solutions in the original grammar, but terminate if a
  maximum number of rounds for reconstruction is exceeded.
+ all (default)
  Try to reconstruct solutions in the original grammar. In this mode, we do not
  terminate until a solution is successfully reconstructed.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-si-rcons: `") +
                        optarg + "'.  Try --sygus-si-rcons=help.");
}
std::ostream& operator<<(std::ostream& os, SygusUnifPiMode mode)
{
  switch(mode)
  {
    case SygusUnifPiMode::NONE: return os << "none";
    case SygusUnifPiMode::COMPLETE: return os << "complete";
    case SygusUnifPiMode::CENUM: return os << "cond-enum";
    case SygusUnifPiMode::CENUM_IGAIN: return os << "cond-enum-igain";
    default: Unreachable();
  }
  return os;
}
SygusUnifPiMode stringToSygusUnifPiMode(const std::string& optarg)
{
  if (optarg == "none") return SygusUnifPiMode::NONE;
  else if (optarg == "complete") return SygusUnifPiMode::COMPLETE;
  else if (optarg == "cond-enum") return SygusUnifPiMode::CENUM;
  else if (optarg == "cond-enum-igain") return SygusUnifPiMode::CENUM_IGAIN;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for piecewise-independent unification.
Available modes for --sygus-unif-pi are:
+ none (default)
  Do not use piecewise-independent unification.
+ complete
  Use complete approach for piecewise-independent unification (see Section 3 of
  Barbosa et al FMCAD 2019)
+ cond-enum
  Use unconstrained condition enumeration for piecewise-independent unification
  (see Section 4 of Barbosa et al FMCAD 2019).
+ cond-enum-igain
  Same as cond-enum, but additionally uses an information gain heuristic when
  doing decision tree learning.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-unif-pi: `") +
                        optarg + "'.  Try --sygus-unif-pi=help.");
}
std::ostream& operator<<(std::ostream& os, TermDbMode mode)
{
  switch(mode)
  {
    case TermDbMode::ALL: return os << "all";
    case TermDbMode::RELEVANT: return os << "relevant";
    default: Unreachable();
  }
  return os;
}
TermDbMode stringToTermDbMode(const std::string& optarg)
{
  if (optarg == "all") return TermDbMode::ALL;
  else if (optarg == "relevant") return TermDbMode::RELEVANT;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for terms included in the quantifiers term database.
Available modes for --term-db-mode are:
+ all (default)
  Quantifiers module considers all ground terms.
+ relevant
  Quantifiers module considers only ground terms connected to current
  assertions.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --term-db-mode: `") +
                        optarg + "'.  Try --term-db-mode=help.");
}
std::ostream& operator<<(std::ostream& os, TriggerActiveSelMode mode)
{
  switch(mode)
  {
    case TriggerActiveSelMode::ALL: return os << "all";
    case TriggerActiveSelMode::MIN: return os << "min";
    case TriggerActiveSelMode::MAX: return os << "max";
    default: Unreachable();
  }
  return os;
}
TriggerActiveSelMode stringToTriggerActiveSelMode(const std::string& optarg)
{
  if (optarg == "all") return TriggerActiveSelMode::ALL;
  else if (optarg == "min") return TriggerActiveSelMode::MIN;
  else if (optarg == "max") return TriggerActiveSelMode::MAX;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Trigger active selection modes.
Available modes for --trigger-active-sel are:
+ all (default)
  Make all triggers active.
+ min
  Activate triggers with minimal ground terms.
+ max
  Activate triggers with maximal ground terms.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --trigger-active-sel: `") +
                        optarg + "'.  Try --trigger-active-sel=help.");
}
std::ostream& operator<<(std::ostream& os, TriggerSelMode mode)
{
  switch(mode)
  {
    case TriggerSelMode::MIN: return os << "min";
    case TriggerSelMode::MAX: return os << "max";
    case TriggerSelMode::MIN_SINGLE_MAX: return os << "min-s-max";
    case TriggerSelMode::MIN_SINGLE_ALL: return os << "min-s-all";
    case TriggerSelMode::ALL: return os << "all";
    default: Unreachable();
  }
  return os;
}
TriggerSelMode stringToTriggerSelMode(const std::string& optarg)
{
  if (optarg == "min") return TriggerSelMode::MIN;
  else if (optarg == "max") return TriggerSelMode::MAX;
  else if (optarg == "min-s-max") return TriggerSelMode::MIN_SINGLE_MAX;
  else if (optarg == "min-s-all") return TriggerSelMode::MIN_SINGLE_ALL;
  else if (optarg == "all") return TriggerSelMode::ALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Trigger selection modes.
Available modes for --trigger-sel are:
+ min (default)
  Consider only minimal subterms that meet criteria for triggers.
+ max
  Consider only maximal subterms that meet criteria for triggers.
+ min-s-max
  Consider only minimal subterms that meet criteria for single triggers, maximal
  otherwise.
+ min-s-all
  Consider only minimal subterms that meet criteria for single triggers, all
  otherwise.
+ all
  Consider all subterms that meet criteria for triggers.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --trigger-sel: `") +
                        optarg + "'.  Try --trigger-sel=help.");
}
std::ostream& operator<<(std::ostream& os, UserPatMode mode)
{
  switch(mode)
  {
    case UserPatMode::USE: return os << "use";
    case UserPatMode::TRUST: return os << "trust";
    case UserPatMode::STRICT: return os << "strict";
    case UserPatMode::RESORT: return os << "resort";
    case UserPatMode::IGNORE: return os << "ignore";
    case UserPatMode::INTERLEAVE: return os << "interleave";
    default: Unreachable();
  }
  return os;
}
UserPatMode stringToUserPatMode(const std::string& optarg)
{
  if (optarg == "use") return UserPatMode::USE;
  else if (optarg == "trust") return UserPatMode::TRUST;
  else if (optarg == "strict") return UserPatMode::STRICT;
  else if (optarg == "resort") return UserPatMode::RESORT;
  else if (optarg == "ignore") return UserPatMode::IGNORE;
  else if (optarg == "interleave") return UserPatMode::INTERLEAVE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  These modes determine how user provided patterns (triggers) are used during
  E-matching. The modes vary on when instantiation based on user-provided
  triggers is combined with instantiation based on automatically selected
  triggers.
Available modes for --user-pat are:
+ use
  Use both user-provided and auto-generated patterns when patterns are provided
  for a quantified formula.
+ trust (default)
  When provided, use only user-provided patterns for a quantified formula.
+ strict
  When provided, use only user-provided patterns for a quantified formula, and
  do not use any other instantiation techniques.
+ resort
  Use user-provided patterns only after auto-generated patterns saturate.
+ ignore
  Ignore user-provided patterns.
+ interleave
  Alternate between use/resort.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --user-pat: `") +
                        optarg + "'.  Try --user-pat=help.");
}
std::ostream& operator<<(std::ostream& os, UserPoolMode mode)
{
  switch(mode)
  {
    case UserPoolMode::USE: return os << "use";
    case UserPoolMode::TRUST: return os << "trust";
    case UserPoolMode::IGNORE: return os << "ignore";
    default: Unreachable();
  }
  return os;
}
UserPoolMode stringToUserPoolMode(const std::string& optarg)
{
  if (optarg == "use") return UserPoolMode::USE;
  else if (optarg == "trust") return UserPoolMode::TRUST;
  else if (optarg == "ignore") return UserPoolMode::IGNORE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  These modes determine how user provided pools are used in combination with
  other instantiation techniques.
Available modes for --user-pool are:
+ use
  Use both user-provided pool and other instantiation strategies when pools are
  provided for a quantified formula.
+ trust (default)
  When provided, use only user-provided pool for a quantified formula.
+ ignore
  Ignore user-provided pool.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --user-pool: `") +
                        optarg + "'.  Try --user-pool=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
