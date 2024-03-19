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

#ifndef CVC5__OPTIONS__PROOF_H
#define CVC5__OPTIONS__PROOF_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class ProofCheckMode
{
  EAGER, EAGER_SIMPLE, LAZY, NONE,
  __MAX_VALUE = NONE
};
std::ostream& operator<<(std::ostream& os, ProofCheckMode mode);
ProofCheckMode stringToProofCheckMode(const std::string& optarg);

enum class ProofFormatMode
{
  NONE, DOT, LFSC, ALETHE, TPTP,
  __MAX_VALUE = TPTP
};
std::ostream& operator<<(std::ostream& os, ProofFormatMode mode);
ProofFormatMode stringToProofFormatMode(const std::string& optarg);

enum class ProofGranularityMode
{
  MACRO, REWRITE, THEORY_REWRITE, DSL_REWRITE,
  __MAX_VALUE = DSL_REWRITE
};
std::ostream& operator<<(std::ostream& os, ProofGranularityMode mode);
ProofGranularityMode stringToProofGranularityMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderPROOF
{
// clang-format off
  bool checkProofSteps = false;
  bool checkProofStepsWasSetByUser = false;
  bool lfscExpandTrust = false;
  bool lfscExpandTrustWasSetByUser = false;
  bool lfscFlatten = false;
  bool lfscFlattenWasSetByUser = false;
  bool optResReconSize = true;
  bool optResReconSizeWasSetByUser = false;
  bool printDotClusters = false;
  bool printDotClustersWasSetByUser = false;
  bool proofAletheResPivots = false;
  bool proofAletheResPivotsWasSetByUser = false;
  bool proofAnnotate = false;
  bool proofAnnotateWasSetByUser = false;
  ProofCheckMode proofCheck = ProofCheckMode::NONE;
  bool proofCheckWasSetByUser = false;
  bool printDotAsDAG = false;
  bool printDotAsDAGWasSetByUser = false;
  ProofFormatMode proofFormatMode = ProofFormatMode::NONE;
  bool proofFormatModeWasSetByUser = false;
  ProofGranularityMode proofGranularityMode = ProofGranularityMode::MACRO;
  bool proofGranularityModeWasSetByUser = false;
  uint64_t proofPedantic = 0;
  bool proofPedanticWasSetByUser = false;
  bool proofPpMerge = true;
  bool proofPpMergeWasSetByUser = false;
  bool proofPrintConclusion = false;
  bool proofPrintConclusionWasSetByUser = false;
  bool proofPruneInput = false;
  bool proofPruneInputWasSetByUser = false;
  int64_t proofRewriteRconsRecLimit = 5;
  bool proofRewriteRconsRecLimitWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__PROOF_H */
