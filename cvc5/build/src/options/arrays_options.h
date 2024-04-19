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

#ifndef CVC5__OPTIONS__ARRAYS_H
#define CVC5__OPTIONS__ARRAYS_H

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

struct HolderARRAYS
{
// clang-format off
  bool arraysEagerIndexSplitting = true;
  bool arraysEagerIndexSplittingWasSetByUser = false;
  bool arraysEagerLemmas = false;
  bool arraysEagerLemmasWasSetByUser = false;
  bool arraysExp = false;
  bool arraysExpWasSetByUser = false;
  bool arraysOptimizeLinear = true;
  bool arraysOptimizeLinearWasSetByUser = false;
  int64_t arraysPropagate = 2;
  bool arraysPropagateWasSetByUser = false;
  bool arraysReduceSharing = false;
  bool arraysReduceSharingWasSetByUser = false;
  bool arraysWeakEquivalence = false;
  bool arraysWeakEquivalenceWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__ARRAYS_H */
