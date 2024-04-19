/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Contains code for handling command-line options.
 *
 * For each <module>_options.toml configuration file, mkoptions.py
 * expands this template and generates a <module>_options.h file.
 */

#include "cvc5_private.h"

#ifndef CVC5__OPTIONS__BV_H
#define CVC5__OPTIONS__BV_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class BitblastMode
{
  LAZY, EAGER,
  __MAX_VALUE = EAGER
};
std::ostream& operator<<(std::ostream& os, BitblastMode mode);
BitblastMode stringToBitblastMode(const std::string& optarg);

enum class BoolToBVMode
{
  OFF, ITE, ALL,
  __MAX_VALUE = ALL
};
std::ostream& operator<<(std::ostream& os, BoolToBVMode mode);
BoolToBVMode stringToBoolToBVMode(const std::string& optarg);

enum class SatSolverMode
{
  MINISAT, CRYPTOMINISAT, CADICAL, KISSAT,
  __MAX_VALUE = KISSAT
};
std::ostream& operator<<(std::ostream& os, SatSolverMode mode);
SatSolverMode stringToSatSolverMode(const std::string& optarg);

enum class BVSolver
{
  BITBLAST, BITBLAST_INTERNAL,
  __MAX_VALUE = BITBLAST_INTERNAL
};
std::ostream& operator<<(std::ostream& os, BVSolver mode);
BVSolver stringToBVSolver(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderBV
{
// clang-format off
  BitblastMode bitblastMode = BitblastMode::LAZY;
  bool bitblastModeWasSetByUser = false;
  bool bitwiseEq = true;
  bool bitwiseEqWasSetByUser = false;
  BoolToBVMode boolToBitvector = BoolToBVMode::OFF;
  bool boolToBitvectorWasSetByUser = false;
  bool bvAssertInput = false;
  bool bvAssertInputWasSetByUser = false;
  bool bvEagerEval = false;
  bool bvEagerEvalWasSetByUser = false;
  bool bvGaussElim = false;
  bool bvGaussElimWasSetByUser = false;
  bool bvIntroducePow2 = false;
  bool bvIntroducePow2WasSetByUser = false;
  bool bitvectorPropagate = true;
  bool bitvectorPropagateWasSetByUser = false;
  bool rwExtendEq = false;
  bool rwExtendEqWasSetByUser = false;
  SatSolverMode bvSatSolver = SatSolverMode::CADICAL;
  bool bvSatSolverWasSetByUser = false;
  BVSolver bvSolver = BVSolver::BITBLAST;
  bool bvSolverWasSetByUser = false;
  bool bitvectorToBool = false;
  bool bitvectorToBoolWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__BV_H */
