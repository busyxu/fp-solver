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

#ifndef CVC5__OPTIONS__PROP_H
#define CVC5__OPTIONS__PROP_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class MinisatSimpMode
{
  ALL, CLAUSE_ELIM, NONE,
  __MAX_VALUE = NONE
};
std::ostream& operator<<(std::ostream& os, MinisatSimpMode mode);
MinisatSimpMode stringToMinisatSimpMode(const std::string& optarg);

enum class PreRegisterMode
{
  EAGER, LAZY,
  __MAX_VALUE = LAZY
};
std::ostream& operator<<(std::ostream& os, PreRegisterMode mode);
PreRegisterMode stringToPreRegisterMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderPROP
{
// clang-format off
  bool minisatDumpDimacs = false;
  bool minisatDumpDimacsWasSetByUser = false;
  MinisatSimpMode minisatSimpMode = MinisatSimpMode::ALL;
  bool minisatSimpModeWasSetByUser = false;
  PreRegisterMode preRegisterMode = PreRegisterMode::EAGER;
  bool preRegisterModeWasSetByUser = false;
  double satRandomFreq = 0.0;
  bool satRandomFreqWasSetByUser = false;
  uint64_t satRestartFirst = 25;
  bool satRestartFirstWasSetByUser = false;
  double satRestartInc = 3.0;
  bool satRestartIncWasSetByUser = false;
  uint64_t satRandomSeed = 0;
  bool satRandomSeedWasSetByUser = false;
  double satVarDecay = 0.95;
  bool satVarDecayWasSetByUser = false;
  double satClauseDecay = 0.999;
  bool satClauseDecayWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__PROP_H */
