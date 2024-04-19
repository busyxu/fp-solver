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

#ifndef CVC5__OPTIONS__DRIVER_H
#define CVC5__OPTIONS__DRIVER_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderDRIVER
{
// clang-format off
  bool showCopyright = false;
  bool showCopyrightWasSetByUser = false;
  bool dumpDifficulty = false;
  bool dumpDifficultyWasSetByUser = false;
  bool dumpInstantiations = false;
  bool dumpInstantiationsWasSetByUser = false;
  bool dumpInstantiationsDebug = false;
  bool dumpInstantiationsDebugWasSetByUser = false;
  bool dumpModels = false;
  bool dumpModelsWasSetByUser = false;
  bool dumpProofs = false;
  bool dumpProofsWasSetByUser = false;
  bool dumpUnsatCores = false;
  bool dumpUnsatCoresWasSetByUser = false;
  bool earlyExit = true;
  bool earlyExitWasSetByUser = false;
  std::string filename = "";
  bool filenameWasSetByUser = false;
  bool forceNoLimitCpuWhileDump = false;
  bool forceNoLimitCpuWhileDumpWasSetByUser = false;
  bool help = false;
  bool helpWasSetByUser = false;
  bool interactive = false;
  bool interactiveWasSetByUser = false;
  uint64_t portfolioJobs = 1;
  bool portfolioJobsWasSetByUser = false;
  bool printSuccess = false;
  bool printSuccessWasSetByUser = false;
  uint64_t seed = 0;
  bool seedWasSetByUser = false;
  bool segvSpin = false;
  bool segvSpinWasSetByUser = false;
  bool showConfiguration = false;
  bool showConfigurationWasSetByUser = false;
  bool showTraceTags = false;
  bool showTraceTagsWasSetByUser = false;
  bool stdinInputPerLine = true;
  bool stdinInputPerLineWasSetByUser = false;
  bool usePortfolio = false;
  bool usePortfolioWasSetByUser = false;
  bool showVersion = false;
  bool showVersionWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__DRIVER_H */
