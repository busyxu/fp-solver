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

#ifndef CVC5__OPTIONS__BASE_H
#define CVC5__OPTIONS__BASE_H

#include "options/options.h"

// clang-format off
#include "options/language.h"
#include "options/managed_streams.h"
#include <bitset>
#include <iostream>
// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class OutputTag
{
  NONE, INST, SYGUS, SYGUS_GRAMMAR, SYGUS_SOL_GTERM, TRIGGER, RAW_BENCHMARK,
  LEARNED_LITS, SUBS, POST_ASSERTS, PRE_ASSERTS, DEEP_RESTART, INCOMPLETE,
  LEMMAS, TRUSTED_PROOF_STEPS,
  __MAX_VALUE = TRUSTED_PROOF_STEPS
};
std::ostream& operator<<(std::ostream& os, OutputTag mode);
OutputTag stringToOutputTag(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderBASE
{
// clang-format off
  ManagedErr err = {};
  bool errWasSetByUser = false;
  ManagedIn in = {};
  bool inWasSetByUser = false;
  bool incrementalSolving = true;
  bool incrementalSolvingWasSetByUser = false;
  Language inputLanguage = Language::LANG_AUTO;
  bool inputLanguageWasSetByUser = false;
  ManagedOut out = {};
  bool outWasSetByUser = false;
  bool parseOnly = false;
  bool parseOnlyWasSetByUser = false;
  bool preprocessOnly = false;
  bool preprocessOnlyWasSetByUser = false;
  uint64_t cumulativeResourceLimit = 0;
  bool cumulativeResourceLimitWasSetByUser = false;
  uint64_t perCallResourceLimit = 0;
  bool perCallResourceLimitWasSetByUser = false;
  bool statistics = false;
  bool statisticsWasSetByUser = false;
  bool statisticsAll = false;
  bool statisticsAllWasSetByUser = false;
  bool statisticsEveryQuery = false;
  bool statisticsEveryQueryWasSetByUser = false;
  bool statisticsInternal = false;
  bool statisticsInternalWasSetByUser = false;
  uint64_t cumulativeMillisecondLimit = 0;
  bool cumulativeMillisecondLimitWasSetByUser = false;
  uint64_t perCallMillisecondLimit = 0;
  bool perCallMillisecondLimitWasSetByUser = false;
  int64_t verbosity = 0;
  bool verbosityWasSetByUser = false;
  std::bitset<static_cast<size_t>(OutputTag::__MAX_VALUE)+1> outputTagHolder = {};
  bool outputTagHolderWasSetByUser = false;
  std::vector<std::string> resourceWeightHolder = {};
  bool resourceWeightHolderWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__BASE_H */
