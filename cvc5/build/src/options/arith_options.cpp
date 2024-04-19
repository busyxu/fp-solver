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
#include "options/arith_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, ArithPropagationMode mode)
{
  switch(mode)
  {
    case ArithPropagationMode::NO_PROP: return os << "none";
    case ArithPropagationMode::UNATE_PROP: return os << "unate";
    case ArithPropagationMode::BOUND_INFERENCE_PROP: return os << "bi";
    case ArithPropagationMode::BOTH_PROP: return os << "both";
    default: Unreachable();
  }
  return os;
}
ArithPropagationMode stringToArithPropagationMode(const std::string& optarg)
{
  if (optarg == "none") return ArithPropagationMode::NO_PROP;
  else if (optarg == "unate") return ArithPropagationMode::UNATE_PROP;
  else if (optarg == "bi") return ArithPropagationMode::BOUND_INFERENCE_PROP;
  else if (optarg == "both") return ArithPropagationMode::BOTH_PROP;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  This decides on kind of propagation arithmetic attempts to do during the
  search.
Available modes for --arith-prop are:
+ unate
  Use constraints to do unate propagation.
+ bi
  (Bounds Inference) infers bounds on basic variables using the upper and lower
  bounds of the non-basic variables in the tableau.
+ both (default)
  Use bounds inference and unate.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --arith-prop: `") +
                        optarg + "'.  Try --arith-prop=help.");
}
std::ostream& operator<<(std::ostream& os, ErrorSelectionRule mode)
{
  switch(mode)
  {
    case ErrorSelectionRule::MINIMUM_AMOUNT: return os << "min";
    case ErrorSelectionRule::VAR_ORDER: return os << "varord";
    case ErrorSelectionRule::MAXIMUM_AMOUNT: return os << "max";
    case ErrorSelectionRule::SUM_METRIC: return os << "sum";
    default: Unreachable();
  }
  return os;
}
ErrorSelectionRule stringToErrorSelectionRule(const std::string& optarg)
{
  if (optarg == "min") return ErrorSelectionRule::MINIMUM_AMOUNT;
  else if (optarg == "varord") return ErrorSelectionRule::VAR_ORDER;
  else if (optarg == "max") return ErrorSelectionRule::MAXIMUM_AMOUNT;
  else if (optarg == "sum") return ErrorSelectionRule::SUM_METRIC;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  This decides on the rule used by simplex during heuristic rounds for deciding
  the next basic variable to select.
Available rules for --error-selection-rule are:
+ min (default)
  The minimum abs() value of the variable's violation of its bound.
+ varord
  The variable order.
+ max
  The maximum violation the bound.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --error-selection-rule: `") +
                        optarg + "'.  Try --error-selection-rule=help.");
}
std::ostream& operator<<(std::ostream& os, nlCovLiftingMode mode)
{
  switch(mode)
  {
    case nlCovLiftingMode::REGULAR: return os << "regular";
    case nlCovLiftingMode::LAZARD: return os << "lazard";
    default: Unreachable();
  }
  return os;
}
nlCovLiftingMode stringTonlCovLiftingMode(const std::string& optarg)
{
  if (optarg == "regular") return nlCovLiftingMode::REGULAR;
  else if (optarg == "lazard") return nlCovLiftingMode::LAZARD;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for the Coverings lifting in non-linear arithmetic.
Available modes for --nl-cov-lift are:
+ regular (default)
  Regular lifting.
+ lazard
  Lazard's lifting scheme.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --nl-cov-lift: `") +
                        optarg + "'.  Try --nl-cov-lift=help.");
}
std::ostream& operator<<(std::ostream& os, nlCovLinearModelMode mode)
{
  switch(mode)
  {
    case nlCovLinearModelMode::NONE: return os << "none";
    case nlCovLinearModelMode::INITIAL: return os << "initial";
    case nlCovLinearModelMode::PERSISTENT: return os << "persistent";
    default: Unreachable();
  }
  return os;
}
nlCovLinearModelMode stringTonlCovLinearModelMode(const std::string& optarg)
{
  if (optarg == "none") return nlCovLinearModelMode::NONE;
  else if (optarg == "initial") return nlCovLinearModelMode::INITIAL;
  else if (optarg == "persistent") return nlCovLinearModelMode::PERSISTENT;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for the usage of the linear model in non-linear arithmetic.
Available modes for --nl-cov-linear-model are:
+ none (default)
  Do not use linear model to seed nonlinear model
+ initial
  Use linear model to seed nonlinear model initially, discard it when it does
  not work
+ persistent
  Use linear model to seed nonlinear model whenever possible
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --nl-cov-linear-model: `") +
                        optarg + "'.  Try --nl-cov-linear-model=help.");
}
std::ostream& operator<<(std::ostream& os, nlCovProjectionMode mode)
{
  switch(mode)
  {
    case nlCovProjectionMode::MCCALLUM: return os << "mccallum";
    case nlCovProjectionMode::LAZARD: return os << "lazard";
    case nlCovProjectionMode::LAZARDMOD: return os << "lazard-mod";
    default: Unreachable();
  }
  return os;
}
nlCovProjectionMode stringTonlCovProjectionMode(const std::string& optarg)
{
  if (optarg == "mccallum") return nlCovProjectionMode::MCCALLUM;
  else if (optarg == "lazard") return nlCovProjectionMode::LAZARD;
  else if (optarg == "lazard-mod") return nlCovProjectionMode::LAZARDMOD;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for the Coverings projection operator in non-linear arithmetic.
Available modes for --nl-cov-proj are:
+ mccallum (default)
  McCallum's projection operator.
+ lazard
  Lazard's projection operator.
+ lazard-mod
  A modification of Lazard's projection operator.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --nl-cov-proj: `") +
                        optarg + "'.  Try --nl-cov-proj=help.");
}
std::ostream& operator<<(std::ostream& os, NlExtMode mode)
{
  switch(mode)
  {
    case NlExtMode::NONE: return os << "none";
    case NlExtMode::LIGHT: return os << "light";
    case NlExtMode::FULL: return os << "full";
    default: Unreachable();
  }
  return os;
}
NlExtMode stringToNlExtMode(const std::string& optarg)
{
  if (optarg == "none") return NlExtMode::NONE;
  else if (optarg == "light") return NlExtMode::LIGHT;
  else if (optarg == "full") return NlExtMode::FULL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for the non-linear linearization
Available modes for --nl-ext are:
+ none
  Disable linearization approach
+ light
  Only use a few light-weight lemma schemes
+ full (default)
  Use all lemma schemes
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --nl-ext: `") +
                        optarg + "'.  Try --nl-ext=help.");
}
std::ostream& operator<<(std::ostream& os, NlRlvMode mode)
{
  switch(mode)
  {
    case NlRlvMode::NONE: return os << "none";
    case NlRlvMode::INTERLEAVE: return os << "interleave";
    case NlRlvMode::ALWAYS: return os << "always";
    default: Unreachable();
  }
  return os;
}
NlRlvMode stringToNlRlvMode(const std::string& optarg)
{
  if (optarg == "none") return NlRlvMode::NONE;
  else if (optarg == "interleave") return NlRlvMode::INTERLEAVE;
  else if (optarg == "always") return NlRlvMode::ALWAYS;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for using relevance of assertions in non-linear arithmetic.
Available modes for --nl-rlv are:
+ none (default)
  Do not use relevance.
+ interleave
  Alternate rounds using relevance.
+ always
  Always use relevance.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --nl-rlv: `") +
                        optarg + "'.  Try --nl-rlv=help.");
}
std::ostream& operator<<(std::ostream& os, ArithUnateLemmaMode mode)
{
  switch(mode)
  {
    case ArithUnateLemmaMode::ALL: return os << "all";
    case ArithUnateLemmaMode::EQUALITY: return os << "eqs";
    case ArithUnateLemmaMode::INEQUALITY: return os << "ineqs";
    case ArithUnateLemmaMode::NO: return os << "none";
    default: Unreachable();
  }
  return os;
}
ArithUnateLemmaMode stringToArithUnateLemmaMode(const std::string& optarg)
{
  if (optarg == "all") return ArithUnateLemmaMode::ALL;
  else if (optarg == "eqs") return ArithUnateLemmaMode::EQUALITY;
  else if (optarg == "ineqs") return ArithUnateLemmaMode::INEQUALITY;
  else if (optarg == "none") return ArithUnateLemmaMode::NO;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Unate lemmas are generated before SAT search begins using the relationship of
  constant terms and polynomials.
Available modes for --unate-lemmas are:
+ all (default)
  A combination of inequalities and equalities.
+ eqs
  Outputs lemmas of the general forms (= p c) implies (<= p d) for c < d, or (=
  p c) implies (not (= p d)) for c != d.
+ ineqs
  Outputs lemmas of the general form (<= p c) implies (<= p d) for c < d.
+ none
  Do not add unate lemmas.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --unate-lemmas: `") +
                        optarg + "'.  Try --unate-lemmas=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
