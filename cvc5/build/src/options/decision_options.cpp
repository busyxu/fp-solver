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
#include "options/decision_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, DecisionMode mode)
{
  switch(mode)
  {
    case DecisionMode::INTERNAL: return os << "internal";
    case DecisionMode::JUSTIFICATION: return os << "justification";
    case DecisionMode::STOPONLY: return os << "stoponly";
    default: Unreachable();
  }
  return os;
}
DecisionMode stringToDecisionMode(const std::string& optarg)
{
  if (optarg == "internal") return DecisionMode::INTERNAL;
  else if (optarg == "justification") return DecisionMode::JUSTIFICATION;
  else if (optarg == "stoponly") return DecisionMode::STOPONLY;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Decision modes.
Available modes for --decision are:
+ internal (default)
  Use the internal decision heuristics of the SAT solver.
+ justification
  An ATGP-inspired justification heuristic.
+ stoponly
  Use the justification heuristic only to stop early, not for decisions.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --decision: `") +
                        optarg + "'.  Try --decision=help.");
}
std::ostream& operator<<(std::ostream& os, JutificationSkolemMode mode)
{
  switch(mode)
  {
    case JutificationSkolemMode::FIRST: return os << "first";
    case JutificationSkolemMode::LAST: return os << "last";
    default: Unreachable();
  }
  return os;
}
JutificationSkolemMode stringToJutificationSkolemMode(const std::string& optarg)
{
  if (optarg == "first") return JutificationSkolemMode::FIRST;
  else if (optarg == "last") return JutificationSkolemMode::LAST;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Policy for when to satisfy skolem definitions in justification heuristic
Available modes for --jh-skolem are:
+ first (default)
  satisfy pending relevant skolem definitions before input assertions
+ last
  satisfy pending relevant skolem definitions after input assertions
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --jh-skolem: `") +
                        optarg + "'.  Try --jh-skolem=help.");
}
std::ostream& operator<<(std::ostream& os, JutificationSkolemRlvMode mode)
{
  switch(mode)
  {
    case JutificationSkolemRlvMode::ASSERT: return os << "assert";
    case JutificationSkolemRlvMode::ALWAYS: return os << "always";
    default: Unreachable();
  }
  return os;
}
JutificationSkolemRlvMode stringToJutificationSkolemRlvMode(const std::string& optarg)
{
  if (optarg == "assert") return JutificationSkolemRlvMode::ASSERT;
  else if (optarg == "always") return JutificationSkolemRlvMode::ALWAYS;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Policy for when to consider skolem definitions relevant in justification
  heuristic
Available modes for --jh-skolem-rlv are:
+ assert (default)
  skolems are relevant when they occur in an asserted literal
+ always
  skolems are always relevant
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --jh-skolem-rlv: `") +
                        optarg + "'.  Try --jh-skolem-rlv=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
