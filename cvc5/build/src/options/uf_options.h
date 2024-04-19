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

#ifndef CVC5__OPTIONS__UF_H
#define CVC5__OPTIONS__UF_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class UfssMode
{
  FULL, NO_MINIMAL, NONE,
  __MAX_VALUE = NONE
};
std::ostream& operator<<(std::ostream& os, UfssMode mode);
UfssMode stringToUfssMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderUF
{
// clang-format off
  bool eagerArithBvConv = false;
  bool eagerArithBvConvWasSetByUser = false;
  bool ufSymmetryBreaker = true;
  bool ufSymmetryBreakerWasSetByUser = false;
  bool ufHoExt = true;
  bool ufHoExtWasSetByUser = false;
  bool ufHoLazyLambdaLift = false;
  bool ufHoLazyLambdaLiftWasSetByUser = false;
  UfssMode ufssMode = UfssMode::FULL;
  bool ufssModeWasSetByUser = false;
  int64_t ufssAbortCardinality = -1;
  bool ufssAbortCardinalityWasSetByUser = false;
  bool ufssFairness = true;
  bool ufssFairnessWasSetByUser = false;
  bool ufssFairnessMonotone = false;
  bool ufssFairnessMonotoneWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__UF_H */
