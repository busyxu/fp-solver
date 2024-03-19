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
#include "options/theory_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, EqEngineMode mode)
{
  switch(mode)
  {
    case EqEngineMode::DISTRIBUTED: return os << "distributed";
    case EqEngineMode::CENTRAL: return os << "central";
    default: Unreachable();
  }
  return os;
}
EqEngineMode stringToEqEngineMode(const std::string& optarg)
{
  if (optarg == "distributed") return EqEngineMode::DISTRIBUTED;
  else if (optarg == "central") return EqEngineMode::CENTRAL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Defines mode for managing equalities across theory solvers.
Available modes for --ee-mode are:
+ distributed (default)
  Each theory maintains its own equality engine.
+ central
  All applicable theories use the central equality engine.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --ee-mode: `") +
                        optarg + "'.  Try --ee-mode=help.");
}
std::ostream& operator<<(std::ostream& os, TcMode mode)
{
  switch(mode)
  {
    case TcMode::CARE_GRAPH: return os << "care-graph";
    default: Unreachable();
  }
  return os;
}
TcMode stringToTcMode(const std::string& optarg)
{
  if (optarg == "care-graph") return TcMode::CARE_GRAPH;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Defines mode for theory combination.
Available modes for --tc-mode are:
+ care-graph (default)
  Use care graphs for theory combination.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --tc-mode: `") +
                        optarg + "'.  Try --tc-mode=help.");
}
std::ostream& operator<<(std::ostream& os, TheoryOfMode mode)
{
  switch(mode)
  {
    case TheoryOfMode::THEORY_OF_TYPE_BASED: return os << "type";
    case TheoryOfMode::THEORY_OF_TERM_BASED: return os << "term";
    default: Unreachable();
  }
  return os;
}
TheoryOfMode stringToTheoryOfMode(const std::string& optarg)
{
  if (optarg == "type") return TheoryOfMode::THEORY_OF_TYPE_BASED;
  else if (optarg == "term") return TheoryOfMode::THEORY_OF_TERM_BASED;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Defines how we associate theories with terms.
Available modes for --theoryof-mode are:
+ type (default)
  Type variables, constants and equalities by type.
+ term
  Type variables as uninterpreted, type constants by theory, equalities by the
  parametric theory.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --theoryof-mode: `") +
                        optarg + "'.  Try --theoryof-mode=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
