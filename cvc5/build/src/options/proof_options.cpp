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
#include "options/proof_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, ProofCheckMode mode)
{
  switch(mode)
  {
    case ProofCheckMode::EAGER: return os << "eager";
    case ProofCheckMode::EAGER_SIMPLE: return os << "eager-simple";
    case ProofCheckMode::LAZY: return os << "lazy";
    case ProofCheckMode::NONE: return os << "none";
    default: Unreachable();
  }
  return os;
}
ProofCheckMode stringToProofCheckMode(const std::string& optarg)
{
  if (optarg == "eager") return ProofCheckMode::EAGER;
  else if (optarg == "eager-simple") return ProofCheckMode::EAGER_SIMPLE;
  else if (optarg == "lazy") return ProofCheckMode::LAZY;
  else if (optarg == "none") return ProofCheckMode::NONE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Internal proof checking modes.
Available modes for --proof-check are:
+ eager
  check rule applications and proofs from generators eagerly for local debugging
+ eager-simple
  check rule applications during construction
+ lazy
  check rule applications only during final proof construction
+ none (default)
  do not check rule applications
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --proof-check: `") +
                        optarg + "'.  Try --proof-check=help.");
}
std::ostream& operator<<(std::ostream& os, ProofFormatMode mode)
{
  switch(mode)
  {
    case ProofFormatMode::NONE: return os << "none";
    case ProofFormatMode::DOT: return os << "dot";
    case ProofFormatMode::LFSC: return os << "lfsc";
    case ProofFormatMode::ALETHE: return os << "alethe";
    case ProofFormatMode::TPTP: return os << "tptp";
    default: Unreachable();
  }
  return os;
}
ProofFormatMode stringToProofFormatMode(const std::string& optarg)
{
  if (optarg == "none") return ProofFormatMode::NONE;
  else if (optarg == "dot") return ProofFormatMode::DOT;
  else if (optarg == "lfsc") return ProofFormatMode::LFSC;
  else if (optarg == "alethe") return ProofFormatMode::ALETHE;
  else if (optarg == "tptp") return ProofFormatMode::TPTP;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Proof format modes.
Available modes for --proof-format-mode are:
+ none (default)
  Do not translate proof output
+ dot
  Output DOT proof
+ lfsc
  Output LFSC proof
+ alethe
  Output Alethe proof
+ tptp
  Output TPTP proof (work in progress)
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --proof-format-mode: `") +
                        optarg + "'.  Try --proof-format-mode=help.");
}
std::ostream& operator<<(std::ostream& os, ProofGranularityMode mode)
{
  switch(mode)
  {
    case ProofGranularityMode::MACRO: return os << "macro";
    case ProofGranularityMode::REWRITE: return os << "rewrite";
    case ProofGranularityMode::THEORY_REWRITE: return os << "theory-rewrite";
    case ProofGranularityMode::DSL_REWRITE: return os << "dsl-rewrite";
    default: Unreachable();
  }
  return os;
}
ProofGranularityMode stringToProofGranularityMode(const std::string& optarg)
{
  if (optarg == "macro") return ProofGranularityMode::MACRO;
  else if (optarg == "rewrite") return ProofGranularityMode::REWRITE;
  else if (optarg == "theory-rewrite") return ProofGranularityMode::THEORY_REWRITE;
  else if (optarg == "dsl-rewrite") return ProofGranularityMode::DSL_REWRITE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for proof granularity.
Available modes for --proof-granularity are:
+ macro (default)
  Allow macros. Do not improve the granularity of proofs.
+ rewrite
  Allow rewrite or substitution steps, expand macros.
+ theory-rewrite
  Allow theory rewrite steps, expand macros, rewrite and substitution steps.
+ dsl-rewrite
  Allow DSL rewrites and evaluation steps, expand macros, rewrite, substitution,
  and theory rewrite steps.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --proof-granularity: `") +
                        optarg + "'.  Try --proof-granularity=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
