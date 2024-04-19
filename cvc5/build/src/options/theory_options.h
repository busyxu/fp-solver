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

#ifndef CVC5__OPTIONS__THEORY_H
#define CVC5__OPTIONS__THEORY_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class EqEngineMode
{
  DISTRIBUTED, CENTRAL,
  __MAX_VALUE = CENTRAL
};
std::ostream& operator<<(std::ostream& os, EqEngineMode mode);
EqEngineMode stringToEqEngineMode(const std::string& optarg);

enum class TcMode
{
  CARE_GRAPH,
  __MAX_VALUE = CARE_GRAPH
};
std::ostream& operator<<(std::ostream& os, TcMode mode);
TcMode stringToTcMode(const std::string& optarg);

enum class TheoryOfMode
{
  THEORY_OF_TYPE_BASED, THEORY_OF_TERM_BASED,
  __MAX_VALUE = THEORY_OF_TERM_BASED
};
std::ostream& operator<<(std::ostream& os, TheoryOfMode mode);
TheoryOfMode stringToTheoryOfMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderTHEORY
{
// clang-format off
  bool assignFunctionValues = true;
  bool assignFunctionValuesWasSetByUser = false;
  bool condenseFunctionValues = true;
  bool condenseFunctionValuesWasSetByUser = false;
  EqEngineMode eeMode = EqEngineMode::DISTRIBUTED;
  bool eeModeWasSetByUser = false;
  bool relevanceFilter = false;
  bool relevanceFilterWasSetByUser = false;
  TcMode tcMode = TcMode::CARE_GRAPH;
  bool tcModeWasSetByUser = false;
  TheoryOfMode theoryOfMode = TheoryOfMode::THEORY_OF_TYPE_BASED;
  bool theoryOfModeWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__THEORY_H */
