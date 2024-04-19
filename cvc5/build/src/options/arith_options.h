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

#ifndef CVC5__OPTIONS__ARITH_H
#define CVC5__OPTIONS__ARITH_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class ArithPropagationMode
{
  NO_PROP, UNATE_PROP, BOUND_INFERENCE_PROP, BOTH_PROP,
  __MAX_VALUE = BOTH_PROP
};
std::ostream& operator<<(std::ostream& os, ArithPropagationMode mode);
ArithPropagationMode stringToArithPropagationMode(const std::string& optarg);

enum class ErrorSelectionRule
{
  MINIMUM_AMOUNT, VAR_ORDER, MAXIMUM_AMOUNT, SUM_METRIC,
  __MAX_VALUE = SUM_METRIC
};
std::ostream& operator<<(std::ostream& os, ErrorSelectionRule mode);
ErrorSelectionRule stringToErrorSelectionRule(const std::string& optarg);

enum class nlCovLiftingMode
{
  REGULAR, LAZARD,
  __MAX_VALUE = LAZARD
};
std::ostream& operator<<(std::ostream& os, nlCovLiftingMode mode);
nlCovLiftingMode stringTonlCovLiftingMode(const std::string& optarg);

enum class nlCovLinearModelMode
{
  NONE, INITIAL, PERSISTENT,
  __MAX_VALUE = PERSISTENT
};
std::ostream& operator<<(std::ostream& os, nlCovLinearModelMode mode);
nlCovLinearModelMode stringTonlCovLinearModelMode(const std::string& optarg);

enum class nlCovProjectionMode
{
  MCCALLUM, LAZARD, LAZARDMOD,
  __MAX_VALUE = LAZARDMOD
};
std::ostream& operator<<(std::ostream& os, nlCovProjectionMode mode);
nlCovProjectionMode stringTonlCovProjectionMode(const std::string& optarg);

enum class NlExtMode
{
  NONE, LIGHT, FULL,
  __MAX_VALUE = FULL
};
std::ostream& operator<<(std::ostream& os, NlExtMode mode);
NlExtMode stringToNlExtMode(const std::string& optarg);

enum class NlRlvMode
{
  NONE, INTERLEAVE, ALWAYS,
  __MAX_VALUE = ALWAYS
};
std::ostream& operator<<(std::ostream& os, NlRlvMode mode);
NlRlvMode stringToNlRlvMode(const std::string& optarg);

enum class ArithUnateLemmaMode
{
  ALL, EQUALITY, INEQUALITY, NO,
  __MAX_VALUE = NO
};
std::ostream& operator<<(std::ostream& os, ArithUnateLemmaMode mode);
ArithUnateLemmaMode stringToArithUnateLemmaMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderARITH
{
// clang-format off
  int64_t maxApproxDepth = 200;
  bool maxApproxDepthWasSetByUser = false;
  bool brabTest = true;
  bool brabTestWasSetByUser = false;
  bool arithEqSolver = false;
  bool arithEqSolverWasSetByUser = false;
  bool arithNoPartialFun = false;
  bool arithNoPartialFunWasSetByUser = false;
  ArithPropagationMode arithPropagationMode = ArithPropagationMode::BOTH_PROP;
  bool arithPropagationModeWasSetByUser = false;
  uint64_t arithPropAsLemmaLength = 8;
  bool arithPropAsLemmaLengthWasSetByUser = false;
  bool arithRewriteEq = false;
  bool arithRewriteEqWasSetByUser = false;
  bool arithStaticLearning = true;
  bool arithStaticLearningWasSetByUser = false;
  bool collectPivots = false;
  bool collectPivotsWasSetByUser = false;
  bool doCutAllBounded = false;
  bool doCutAllBoundedWasSetByUser = false;
  bool exportDioDecompositions = false;
  bool exportDioDecompositionsWasSetByUser = false;
  bool arithDioSolver = true;
  bool arithDioSolverWasSetByUser = false;
  int64_t dioSolverTurns = 10;
  bool dioSolverTurnsWasSetByUser = false;
  ErrorSelectionRule arithErrorSelectionRule = ErrorSelectionRule::MINIMUM_AMOUNT;
  bool arithErrorSelectionRuleWasSetByUser = false;
  bool havePenalties = false;
  bool havePenaltiesWasSetByUser = false;
  int64_t arithHeuristicPivots = 0;
  bool arithHeuristicPivotsWasSetByUser = false;
  bool replayFailureLemma = false;
  bool replayFailureLemmaWasSetByUser = false;
  uint64_t maxCutsInContext = 65535;
  bool maxCutsInContextWasSetByUser = false;
  bool arithMLTrick = false;
  bool arithMLTrickWasSetByUser = false;
  uint64_t arithMLTrickSubstitutions = 1;
  bool arithMLTrickSubstitutionsWasSetByUser = false;
  bool newProp = true;
  bool newPropWasSetByUser = false;
  bool nlCov = false;
  bool nlCovWasSetByUser = false;
  bool nlCovForce = false;
  bool nlCovForceWasSetByUser = false;
  nlCovLiftingMode nlCovLifting = nlCovLiftingMode::REGULAR;
  bool nlCovLiftingWasSetByUser = false;
  nlCovLinearModelMode nlCovLinearModel = nlCovLinearModelMode::NONE;
  bool nlCovLinearModelWasSetByUser = false;
  nlCovProjectionMode nlCovProjection = nlCovProjectionMode::MCCALLUM;
  bool nlCovProjectionWasSetByUser = false;
  bool nlCovPrune = false;
  bool nlCovPruneWasSetByUser = false;
  bool nlCovVarElim = true;
  bool nlCovVarElimWasSetByUser = false;
  NlExtMode nlExt = NlExtMode::FULL;
  bool nlExtWasSetByUser = false;
  bool nlExtEntailConflicts = false;
  bool nlExtEntailConflictsWasSetByUser = false;
  bool nlExtFactor = true;
  bool nlExtFactorWasSetByUser = false;
  bool nlExtIncPrecision = true;
  bool nlExtIncPrecisionWasSetByUser = false;
  bool nlExtPurify = false;
  bool nlExtPurifyWasSetByUser = false;
  bool nlExtResBound = false;
  bool nlExtResBoundWasSetByUser = false;
  bool nlExtRewrites = true;
  bool nlExtRewritesWasSetByUser = false;
  bool nlExtSplitZero = false;
  bool nlExtSplitZeroWasSetByUser = false;
  int64_t nlExtTfTaylorDegree = 4;
  bool nlExtTfTaylorDegreeWasSetByUser = false;
  bool nlExtTfTangentPlanes = true;
  bool nlExtTfTangentPlanesWasSetByUser = false;
  bool nlExtTangentPlanes = true;
  bool nlExtTangentPlanesWasSetByUser = false;
  bool nlExtTangentPlanesInterleave = false;
  bool nlExtTangentPlanesInterleaveWasSetByUser = false;
  bool nlICP = false;
  bool nlICPWasSetByUser = false;
  NlRlvMode nlRlvMode = NlRlvMode::NONE;
  bool nlRlvModeWasSetByUser = false;
  bool nlRlvAssertBounds = false;
  bool nlRlvAssertBoundsWasSetByUser = false;
  bool pbRewrites = false;
  bool pbRewritesWasSetByUser = false;
  uint64_t arithPivotThreshold = 2;
  bool arithPivotThresholdWasSetByUser = false;
  uint64_t ppAssertMaxSubSize = 2;
  bool ppAssertMaxSubSizeWasSetByUser = false;
  uint64_t arithPropagateMaxLength = 16;
  bool arithPropagateMaxLengthWasSetByUser = false;
  int64_t replayEarlyCloseDepths = 1;
  bool replayEarlyCloseDepthsWasSetByUser = false;
  uint64_t lemmaRejectCutSize = 25500;
  bool lemmaRejectCutSizeWasSetByUser = false;
  int64_t replayNumericFailurePenalty = 4194304;
  bool replayNumericFailurePenaltyWasSetByUser = false;
  uint64_t replayRejectCutSize = 25500;
  bool replayRejectCutSizeWasSetByUser = false;
  bool restrictedPivots = true;
  bool restrictedPivotsWasSetByUser = false;
  bool revertArithModels = false;
  bool revertArithModelsWasSetByUser = false;
  int64_t rrTurns = 3;
  bool rrTurnsWasSetByUser = false;
  bool trySolveIntStandardEffort = false;
  bool trySolveIntStandardEffortWasSetByUser = false;
  uint64_t arithSimplexCheckPeriod = 200;
  bool arithSimplexCheckPeriodWasSetByUser = false;
  bool soiQuickExplain = false;
  bool soiQuickExplainWasSetByUser = false;
  int64_t arithStandardCheckVarOrderPivots = -1;
  bool arithStandardCheckVarOrderPivotsWasSetByUser = false;
  ArithUnateLemmaMode arithUnateLemmaMode = ArithUnateLemmaMode::ALL;
  bool arithUnateLemmaModeWasSetByUser = false;
  bool useApprox = false;
  bool useApproxWasSetByUser = false;
  bool useFC = false;
  bool useFCWasSetByUser = false;
  bool useSOI = false;
  bool useSOIWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__ARITH_H */
