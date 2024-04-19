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

#ifndef CVC5__OPTIONS__DECISION_H
#define CVC5__OPTIONS__DECISION_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class DecisionMode
{
  INTERNAL, JUSTIFICATION, STOPONLY,
  __MAX_VALUE = STOPONLY
};
std::ostream& operator<<(std::ostream& os, DecisionMode mode);
DecisionMode stringToDecisionMode(const std::string& optarg);

enum class JutificationSkolemMode
{
  FIRST, LAST,
  __MAX_VALUE = LAST
};
std::ostream& operator<<(std::ostream& os, JutificationSkolemMode mode);
JutificationSkolemMode stringToJutificationSkolemMode(const std::string& optarg);

enum class JutificationSkolemRlvMode
{
  ASSERT, ALWAYS,
  __MAX_VALUE = ALWAYS
};
std::ostream& operator<<(std::ostream& os, JutificationSkolemRlvMode mode);
JutificationSkolemRlvMode stringToJutificationSkolemRlvMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderDECISION
{
// clang-format off
  DecisionMode decisionMode = DecisionMode::INTERNAL;
  bool decisionModeWasSetByUser = false;
  bool jhRlvOrder = false;
  bool jhRlvOrderWasSetByUser = false;
  JutificationSkolemMode jhSkolemMode = JutificationSkolemMode::FIRST;
  bool jhSkolemModeWasSetByUser = false;
  JutificationSkolemRlvMode jhSkolemRlvMode = JutificationSkolemRlvMode::ASSERT;
  bool jhSkolemRlvModeWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__DECISION_H */
