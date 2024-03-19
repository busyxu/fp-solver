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
#include "options/bv_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, BitblastMode mode)
{
  switch(mode)
  {
    case BitblastMode::LAZY: return os << "lazy";
    case BitblastMode::EAGER: return os << "eager";
    default: Unreachable();
  }
  return os;
}
BitblastMode stringToBitblastMode(const std::string& optarg)
{
  if (optarg == "lazy") return BitblastMode::LAZY;
  else if (optarg == "eager") return BitblastMode::EAGER;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Bit-blasting modes.
Available modes for --bitblast are:
+ lazy (default)
  Separate Boolean structure and term reasoning between the core SAT solver and
  the bit-vector SAT solver.
+ eager
  Bitblast eagerly to bit-vector SAT solver.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --bitblast: `") +
                        optarg + "'.  Try --bitblast=help.");
}
std::ostream& operator<<(std::ostream& os, BoolToBVMode mode)
{
  switch(mode)
  {
    case BoolToBVMode::OFF: return os << "off";
    case BoolToBVMode::ITE: return os << "ite";
    case BoolToBVMode::ALL: return os << "all";
    default: Unreachable();
  }
  return os;
}
BoolToBVMode stringToBoolToBVMode(const std::string& optarg)
{
  if (optarg == "off") return BoolToBVMode::OFF;
  else if (optarg == "ite") return BoolToBVMode::ITE;
  else if (optarg == "all") return BoolToBVMode::ALL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  BoolToBV preprocessing pass modes.
Available modes for --bool-to-bv are:
+ off (default)
  Don't push any booleans to width one bit-vectors.
+ ite
  Try to turn ITEs into BITVECTOR_ITE when possible. It can fail per-formula if
  not all sub-formulas can be turned to bit-vectors.
+ all
  Force all booleans to be bit-vectors of width one except at the top level.
  Most aggressive mode.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --bool-to-bv: `") +
                        optarg + "'.  Try --bool-to-bv=help.");
}
std::ostream& operator<<(std::ostream& os, SatSolverMode mode)
{
  switch(mode)
  {
    case SatSolverMode::MINISAT: return os << "minisat";
    case SatSolverMode::CRYPTOMINISAT: return os << "cryptominisat";
    case SatSolverMode::CADICAL: return os << "cadical";
    case SatSolverMode::KISSAT: return os << "kissat";
    default: Unreachable();
  }
  return os;
}
SatSolverMode stringToSatSolverMode(const std::string& optarg)
{
  if (optarg == "minisat") return SatSolverMode::MINISAT;
  else if (optarg == "cryptominisat") return SatSolverMode::CRYPTOMINISAT;
  else if (optarg == "cadical") return SatSolverMode::CADICAL;
  else if (optarg == "kissat") return SatSolverMode::KISSAT;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  SAT solver for bit-blasting backend.
Available modes for --bv-sat-solver are:
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --bv-sat-solver: `") +
                        optarg + "'.  Try --bv-sat-solver=help.");
}
std::ostream& operator<<(std::ostream& os, BVSolver mode)
{
  switch(mode)
  {
    case BVSolver::BITBLAST: return os << "bitblast";
    case BVSolver::BITBLAST_INTERNAL: return os << "bitblast-internal";
    default: Unreachable();
  }
  return os;
}
BVSolver stringToBVSolver(const std::string& optarg)
{
  if (optarg == "bitblast") return BVSolver::BITBLAST;
  else if (optarg == "bitblast-internal") return BVSolver::BITBLAST_INTERNAL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Bit-vector solvers.
Available modes for --bv-solver are:
+ bitblast (default)
  Enables bitblasting solver.
+ bitblast-internal
  Enables bitblasting to internal SAT solver with proof support.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --bv-solver: `") +
                        optarg + "'.  Try --bv-solver=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
