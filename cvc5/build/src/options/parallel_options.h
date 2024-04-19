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

#ifndef CVC5__OPTIONS__PARALLEL_H
#define CVC5__OPTIONS__PARALLEL_H

#include "options/options.h"

// clang-format off
#include "options/managed_streams.h"
#include <iostream>
// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class CheckMode
{
  STANDARD, FULL,
  __MAX_VALUE = FULL
};
std::ostream& operator<<(std::ostream& os, CheckMode mode);
CheckMode stringToCheckMode(const std::string& optarg);

enum class PartitionMode
{
  REVISED, STRICT_CUBE, DECISION_TRAIL, HEAP_TRAIL,
  __MAX_VALUE = HEAP_TRAIL
};
std::ostream& operator<<(std::ostream& os, PartitionMode mode);
PartitionMode stringToPartitionMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderPARALLEL
{
// clang-format off
  bool appendLearnedLiteralsToCubes = false;
  bool appendLearnedLiteralsToCubesWasSetByUser = false;
  uint64_t checksBeforePartitioning = 1;
  bool checksBeforePartitioningWasSetByUser = false;
  uint64_t checksBetweenPartitions = 1;
  bool checksBetweenPartitionsWasSetByUser = false;
  uint64_t computePartitions = 0;
  bool computePartitionsWasSetByUser = false;
  CheckMode partitionCheck = CheckMode::STANDARD;
  bool partitionCheckWasSetByUser = false;
  uint64_t partitionConflictSize = 0;
  bool partitionConflictSizeWasSetByUser = false;
  PartitionMode partitionStrategy = PartitionMode::REVISED;
  bool partitionStrategyWasSetByUser = false;
  ManagedOut partitionsOut = ManagedOut();
  bool partitionsOutWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__PARALLEL_H */
