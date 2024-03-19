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
#include "options/prop_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, MinisatSimpMode mode)
{
  switch(mode)
  {
    case MinisatSimpMode::ALL: return os << "all";
    case MinisatSimpMode::CLAUSE_ELIM: return os << "clause-elim";
    case MinisatSimpMode::NONE: return os << "none";
    default: Unreachable();
  }
  return os;
}
MinisatSimpMode stringToMinisatSimpMode(const std::string& optarg)
{
  if (optarg == "all") return MinisatSimpMode::ALL;
  else if (optarg == "clause-elim") return MinisatSimpMode::CLAUSE_ELIM;
  else if (optarg == "none") return MinisatSimpMode::NONE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for Minisat simplifications.
Available modes for --minisat-simplification are:
+ all (default)
  Variable and clause elimination, plus other simplifications.
+ clause-elim
  Caluse elimination and other simplifications, except variable elimination.
+ none
  No simplifications.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --minisat-simplification: `") +
                        optarg + "'.  Try --minisat-simplification=help.");
}
std::ostream& operator<<(std::ostream& os, PreRegisterMode mode)
{
  switch(mode)
  {
    case PreRegisterMode::EAGER: return os << "eager";
    case PreRegisterMode::LAZY: return os << "lazy";
    default: Unreachable();
  }
  return os;
}
PreRegisterMode stringToPreRegisterMode(const std::string& optarg)
{
  if (optarg == "eager") return PreRegisterMode::EAGER;
  else if (optarg == "lazy") return PreRegisterMode::LAZY;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for when to preregister literals.
Available modes for --preregister-mode are:
+ eager (default)
  Preregister literals when they are registered as literals in the SAT solver.
+ lazy
  Preregister literals when they are asserted by the SAT solver.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --preregister-mode: `") +
                        optarg + "'.  Try --preregister-mode=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
