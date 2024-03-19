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
#include "options/smt_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, DeepRestartMode mode)
{
  switch(mode)
  {
    case DeepRestartMode::NONE: return os << "none";
    case DeepRestartMode::INPUT: return os << "input";
    case DeepRestartMode::INPUT_AND_SOLVABLE: return os << "input-and-solvable";
    case DeepRestartMode::INPUT_AND_PROP: return os << "input-and-prop";
    case DeepRestartMode::ALL: return os << "all";
    default: Unreachable();
  }
  return os;
}
DeepRestartMode stringToDeepRestartMode(const std::string& optarg)
{
  if (optarg == "none") return DeepRestartMode::NONE;
  else if (optarg == "input") return DeepRestartMode::INPUT;
  else if (optarg == "input-and-solvable") return DeepRestartMode::INPUT_AND_SOLVABLE;
  else if (optarg == "input-and-prop") return DeepRestartMode::INPUT_AND_PROP;
  else if (optarg == "all") return DeepRestartMode::ALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Mode for deep restarts
Available modes for --deep-restart are:
+ none (default)
  do not use deep restart
+ input
  learn literals that appear in the input
+ input-and-solvable
  learn literals that appear in the input and those that can be solved for
  variables that appear in the input
+ input-and-prop
  learn literals that appear in the input and those that can be solved for
  variables, or correspond to constant propagations for terms that appear in the
  input
+ all
  learn all literals
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --deep-restart: `") +
                        optarg + "'.  Try --deep-restart=help.");
}
std::ostream& operator<<(std::ostream& os, DifficultyMode mode)
{
  switch(mode)
  {
    case DifficultyMode::LEMMA_LITERAL: return os << "lemma-literal";
    case DifficultyMode::LEMMA_LITERAL_ALL: return os << "lemma-literal-all";
    case DifficultyMode::MODEL_CHECK: return os << "model-check";
    default: Unreachable();
  }
  return os;
}
DifficultyMode stringToDifficultyMode(const std::string& optarg)
{
  if (optarg == "lemma-literal") return DifficultyMode::LEMMA_LITERAL;
  else if (optarg == "lemma-literal-all") return DifficultyMode::LEMMA_LITERAL_ALL;
  else if (optarg == "model-check") return DifficultyMode::MODEL_CHECK;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  difficulty output modes.
Available modes for --difficulty-mode are:
+ lemma-literal
  Difficulty of an assertion is how many lemmas (at full effort) use a literal
  that the assertion depends on to be satisfied.
+ lemma-literal-all (default)
  Difficulty of an assertion is how many lemmas use a literal that the assertion
  depends on to be satisfied.
+ model-check
  Difficulty of an assertion is how many times it was not satisfied in a
  candidate model.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --difficulty-mode: `") +
                        optarg + "'.  Try --difficulty-mode=help.");
}
std::ostream& operator<<(std::ostream& os, ExtRewPrepMode mode)
{
  switch(mode)
  {
    case ExtRewPrepMode::OFF: return os << "off";
    case ExtRewPrepMode::USE: return os << "use";
    case ExtRewPrepMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
ExtRewPrepMode stringToExtRewPrepMode(const std::string& optarg)
{
  if (optarg == "off") return ExtRewPrepMode::OFF;
  else if (optarg == "use") return ExtRewPrepMode::USE;
  else if (optarg == "agg") return ExtRewPrepMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  extended rewriter preprocessing pass modes.
Available modes for --ext-rew-prep are:
+ off (default)
  do not use extended rewriter as a preprocessing pass.
+ use
  use extended rewriter as a preprocessing pass.
+ agg
  use aggressive extended rewriter as a preprocessing pass.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --ext-rew-prep: `") +
                        optarg + "'.  Try --ext-rew-prep=help.");
}
std::ostream& operator<<(std::ostream& os, IandMode mode)
{
  switch(mode)
  {
    case IandMode::VALUE: return os << "value";
    case IandMode::SUM: return os << "sum";
    case IandMode::BITWISE: return os << "bitwise";
    default: Unreachable();
  }
  return os;
}
IandMode stringToIandMode(const std::string& optarg)
{
  if (optarg == "value") return IandMode::VALUE;
  else if (optarg == "sum") return IandMode::SUM;
  else if (optarg == "bitwise") return IandMode::BITWISE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Refinement modes for integer AND
Available modes for --iand-mode are:
+ value (default)
  value-based refinement
+ sum
  use sum to represent integer AND in refinement
+ bitwise
  use bitwise comparisons on binary representation of integer for refinement
  (experimental)
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --iand-mode: `") +
                        optarg + "'.  Try --iand-mode=help.");
}
std::ostream& operator<<(std::ostream& os, InterpolantsMode mode)
{
  switch(mode)
  {
    case InterpolantsMode::DEFAULT: return os << "default";
    case InterpolantsMode::ASSUMPTIONS: return os << "assumptions";
    case InterpolantsMode::CONJECTURE: return os << "conjecture";
    case InterpolantsMode::SHARED: return os << "shared";
    case InterpolantsMode::ALL: return os << "all";
    default: Unreachable();
  }
  return os;
}
InterpolantsMode stringToInterpolantsMode(const std::string& optarg)
{
  if (optarg == "default") return InterpolantsMode::DEFAULT;
  else if (optarg == "assumptions") return InterpolantsMode::ASSUMPTIONS;
  else if (optarg == "conjecture") return InterpolantsMode::CONJECTURE;
  else if (optarg == "shared") return InterpolantsMode::SHARED;
  else if (optarg == "all") return InterpolantsMode::ALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Interpolants grammar mode
Available modes for --interpolants-mode are:
+ default
  use the default grammar for the theory or the user-defined grammar if given
+ assumptions
  use only operators that occur in the assumptions
+ conjecture
  use only operators that occur in the conjecture
+ shared
  use only operators that occur both in the assumptions and the conjecture
+ all
  use only operators that occur either in the assumptions or the conjecture
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --interpolants-mode: `") +
                        optarg + "'.  Try --interpolants-mode=help.");
}
std::ostream& operator<<(std::ostream& os, ModelCoresMode mode)
{
  switch(mode)
  {
    case ModelCoresMode::NONE: return os << "none";
    case ModelCoresMode::SIMPLE: return os << "simple";
    case ModelCoresMode::NON_IMPLIED: return os << "non-implied";
    default: Unreachable();
  }
  return os;
}
ModelCoresMode stringToModelCoresMode(const std::string& optarg)
{
  if (optarg == "none") return ModelCoresMode::NONE;
  else if (optarg == "simple") return ModelCoresMode::SIMPLE;
  else if (optarg == "non-implied") return ModelCoresMode::NON_IMPLIED;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Model cores modes.
Available modes for --model-cores are:
+ none (default)
  Do not compute model cores.
+ simple
  Only include a subset of variables whose values are sufficient to show the
  input formula is satisfied by the given model.
+ non-implied
  Only include a subset of variables whose values, in addition to the values of
  variables whose values are implied, are sufficient to show the input formula
  is satisfied by the given model.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --model-cores: `") +
                        optarg + "'.  Try --model-cores=help.");
}
std::ostream& operator<<(std::ostream& os, ProofMode mode)
{
  switch(mode)
  {
    case ProofMode::OFF: return os << "off";
    case ProofMode::PP_ONLY: return os << "pp-only";
    case ProofMode::SAT: return os << "sat-proof";
    case ProofMode::FULL: return os << "full-proof";
    default: Unreachable();
  }
  return os;
}
ProofMode stringToProofMode(const std::string& optarg)
{
  if (optarg == "off") return ProofMode::OFF;
  else if (optarg == "pp-only") return ProofMode::PP_ONLY;
  else if (optarg == "sat-proof") return ProofMode::SAT;
  else if (optarg == "full-proof") return ProofMode::FULL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  proof modes.
Available modes for --proof-mode are:
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --proof-mode: `") +
                        optarg + "'.  Try --proof-mode=help.");
}
std::ostream& operator<<(std::ostream& os, SimplificationMode mode)
{
  switch(mode)
  {
    case SimplificationMode::NONE: return os << "none";
    case SimplificationMode::BATCH: return os << "batch";
    default: Unreachable();
  }
  return os;
}
SimplificationMode stringToSimplificationMode(const std::string& optarg)
{
  if (optarg == "none") return SimplificationMode::NONE;
  else if (optarg == "batch") return SimplificationMode::BATCH;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Simplification modes.
Available modes for --simplification are:
+ none
  Do not perform nonclausal simplification.
+ batch (default)
  Save up all ASSERTions; run nonclausal simplification and clausal (MiniSat)
  propagation for all of them only after reaching a querying command (CHECKSAT
  or QUERY or predicate SUBTYPE declaration).
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --simplification: `") +
                        optarg + "'.  Try --simplification=help.");
}
std::ostream& operator<<(std::ostream& os, SolveBVAsIntMode mode)
{
  switch(mode)
  {
    case SolveBVAsIntMode::OFF: return os << "off";
    case SolveBVAsIntMode::SUM: return os << "sum";
    case SolveBVAsIntMode::IAND: return os << "iand";
    case SolveBVAsIntMode::BV: return os << "bv";
    case SolveBVAsIntMode::BITWISE: return os << "bitwise";
    default: Unreachable();
  }
  return os;
}
SolveBVAsIntMode stringToSolveBVAsIntMode(const std::string& optarg)
{
  if (optarg == "off") return SolveBVAsIntMode::OFF;
  else if (optarg == "sum") return SolveBVAsIntMode::SUM;
  else if (optarg == "iand") return SolveBVAsIntMode::IAND;
  else if (optarg == "bv") return SolveBVAsIntMode::BV;
  else if (optarg == "bitwise") return SolveBVAsIntMode::BITWISE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  solve-bv-as-int modes.
Available modes for --solve-bv-as-int are:
+ off (default)
  Do not translate bit-vectors to integers
+ sum
  Generate a sum expression for each bvand instance, based on the value in
  --solve-bv-as-int-granularity
+ iand
  Translate bvand to the iand operator (experimental)
+ bv
  Translate bvand back to bit-vectors
+ bitwise
  Introduce a UF operator for bvand, and eagerly add bitwise lemmas
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --solve-bv-as-int: `") +
                        optarg + "'.  Try --solve-bv-as-int=help.");
}
std::ostream& operator<<(std::ostream& os, UnsatCoresMode mode)
{
  switch(mode)
  {
    case UnsatCoresMode::OFF: return os << "off";
    case UnsatCoresMode::SAT_PROOF: return os << "sat-proof";
    case UnsatCoresMode::ASSUMPTIONS: return os << "assumptions";
    default: Unreachable();
  }
  return os;
}
UnsatCoresMode stringToUnsatCoresMode(const std::string& optarg)
{
  if (optarg == "off") return UnsatCoresMode::OFF;
  else if (optarg == "sat-proof") return UnsatCoresMode::SAT_PROOF;
  else if (optarg == "assumptions") return UnsatCoresMode::ASSUMPTIONS;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  unsat cores modes.
Available modes for --unsat-cores-mode are:
+ off (default)
  Do not produce unsat cores.
+ sat-proof
  Produce unsat cores from the SAT proof and prepocessing proofs.
+ assumptions
  Produce unsat cores using solving under assumptions and preprocessing proofs.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --unsat-cores-mode: `") +
                        optarg + "'.  Try --unsat-cores-mode=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
