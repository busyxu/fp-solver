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

#ifndef CVC5__OPTIONS__DATATYPES_H
#define CVC5__OPTIONS__DATATYPES_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class SygusFairMode
{
  DIRECT, DT_SIZE, DT_HEIGHT_PRED, DT_SIZE_PRED, NONE,
  __MAX_VALUE = NONE
};
std::ostream& operator<<(std::ostream& os, SygusFairMode mode);
SygusFairMode stringToSygusFairMode(const std::string& optarg);

enum class SygusRewriterMode
{
  NONE, BASIC, EXTENDED,
  __MAX_VALUE = EXTENDED
};
std::ostream& operator<<(std::ostream& os, SygusRewriterMode mode);
SygusRewriterMode stringToSygusRewriterMode(const std::string& optarg);

enum class SygusSimpleSymBreakMode
{
  NONE, BASIC, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, SygusSimpleSymBreakMode mode);
SygusSimpleSymBreakMode stringToSygusSimpleSymBreakMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderDATATYPES
{
// clang-format off
  bool cdtBisimilar = true;
  bool cdtBisimilarWasSetByUser = false;
  bool dtBinarySplit = false;
  bool dtBinarySplitWasSetByUser = false;
  bool dtBlastSplits = false;
  bool dtBlastSplitsWasSetByUser = false;
  bool dtCyclic = true;
  bool dtCyclicWasSetByUser = false;
  bool dtInferAsLemmas = false;
  bool dtInferAsLemmasWasSetByUser = false;
  bool dtNestedRec = false;
  bool dtNestedRecWasSetByUser = false;
  bool dtPoliteOptimize = true;
  bool dtPoliteOptimizeWasSetByUser = false;
  bool dtSharedSelectors = true;
  bool dtSharedSelectorsWasSetByUser = false;
  int64_t sygusAbortSize = -1;
  bool sygusAbortSizeWasSetByUser = false;
  SygusFairMode sygusFair = SygusFairMode::DT_SIZE;
  bool sygusFairWasSetByUser = false;
  bool sygusFairMax = true;
  bool sygusFairMaxWasSetByUser = false;
  SygusRewriterMode sygusRewriter = SygusRewriterMode::EXTENDED;
  bool sygusRewriterWasSetByUser = false;
  SygusSimpleSymBreakMode sygusSimpleSymBreak = SygusSimpleSymBreakMode::AGG;
  bool sygusSimpleSymBreakWasSetByUser = false;
  bool sygusSymBreakLazy = true;
  bool sygusSymBreakLazyWasSetByUser = false;
  bool sygusSymBreakPbe = true;
  bool sygusSymBreakPbeWasSetByUser = false;
  bool sygusSymBreakRlv = true;
  bool sygusSymBreakRlvWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__DATATYPES_H */
