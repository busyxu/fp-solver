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

#ifndef CVC5__OPTIONS__STRINGS_H
#define CVC5__OPTIONS__STRINGS_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class RegExpElimMode
{
  OFF, ON, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, RegExpElimMode mode);
RegExpElimMode stringToRegExpElimMode(const std::string& optarg);

enum class RegExpInterMode
{
  ALL, CONSTANT, ONE_CONSTANT, NONE,
  __MAX_VALUE = NONE
};
std::ostream& operator<<(std::ostream& os, RegExpInterMode mode);
RegExpInterMode stringToRegExpInterMode(const std::string& optarg);

enum class SeqArrayMode
{
  LAZY, EAGER, NONE,
  __MAX_VALUE = NONE
};
std::ostream& operator<<(std::ostream& os, SeqArrayMode mode);
SeqArrayMode stringToSeqArrayMode(const std::string& optarg);

enum class ProcessLoopMode
{
  FULL, SIMPLE, SIMPLE_ABORT, NONE, ABORT,
  __MAX_VALUE = ABORT
};
std::ostream& operator<<(std::ostream& os, ProcessLoopMode mode);
ProcessLoopMode stringToProcessLoopMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderSTRINGS
{
// clang-format off
  RegExpElimMode regExpElim = RegExpElimMode::OFF;
  bool regExpElimWasSetByUser = false;
  RegExpInterMode stringRegExpInterMode = RegExpInterMode::NONE;
  bool stringRegExpInterModeWasSetByUser = false;
  SeqArrayMode seqArray = SeqArrayMode::NONE;
  bool seqArrayWasSetByUser = false;
  uint64_t stringsAlphaCard = 196608;
  bool stringsAlphaCardWasSetByUser = false;
  bool stringCheckEntailLen = true;
  bool stringCheckEntailLenWasSetByUser = false;
  bool stringsCodeElim = false;
  bool stringsCodeElimWasSetByUser = false;
  bool stringsDeqExt = false;
  bool stringsDeqExtWasSetByUser = false;
  bool stringEagerEval = true;
  bool stringEagerEvalWasSetByUser = false;
  bool stringsEagerLenEntRegexp = false;
  bool stringsEagerLenEntRegexpWasSetByUser = false;
  bool stringEagerReg = true;
  bool stringEagerRegWasSetByUser = false;
  bool stringEagerSolver = true;
  bool stringEagerSolverWasSetByUser = false;
  bool stringExp = false;
  bool stringExpWasSetByUser = false;
  bool stringFlatForms = true;
  bool stringFlatFormsWasSetByUser = false;
  bool stringFMF = false;
  bool stringFMFWasSetByUser = false;
  bool stringInferAsLemmas = false;
  bool stringInferAsLemmasWasSetByUser = false;
  bool stringInferSym = true;
  bool stringInferSymWasSetByUser = false;
  bool stringLazyPreproc = true;
  bool stringLazyPreprocWasSetByUser = false;
  bool stringLenNorm = true;
  bool stringLenNormWasSetByUser = false;
  bool stringModelBasedReduction = true;
  bool stringModelBasedReductionWasSetByUser = false;
  uint64_t stringsModelMaxLength = 65536;
  bool stringsModelMaxLengthWasSetByUser = false;
  ProcessLoopMode stringProcessLoopMode = ProcessLoopMode::FULL;
  bool stringProcessLoopModeWasSetByUser = false;
  bool stringRegexpPosConcatEager = false;
  bool stringRegexpPosConcatEagerWasSetByUser = false;
  bool stringRegexpInclusion = true;
  bool stringRegexpInclusionWasSetByUser = false;
  bool stringRExplainLemmas = true;
  bool stringRExplainLemmasWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__STRINGS_H */
