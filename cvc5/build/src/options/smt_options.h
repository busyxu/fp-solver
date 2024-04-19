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

#ifndef CVC5__OPTIONS__SMT_H
#define CVC5__OPTIONS__SMT_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class DeepRestartMode
{
  NONE, INPUT, INPUT_AND_SOLVABLE, INPUT_AND_PROP, ALL,
  __MAX_VALUE = ALL
};
std::ostream& operator<<(std::ostream& os, DeepRestartMode mode);
DeepRestartMode stringToDeepRestartMode(const std::string& optarg);

enum class DifficultyMode
{
  LEMMA_LITERAL, LEMMA_LITERAL_ALL, MODEL_CHECK,
  __MAX_VALUE = MODEL_CHECK
};
std::ostream& operator<<(std::ostream& os, DifficultyMode mode);
DifficultyMode stringToDifficultyMode(const std::string& optarg);

enum class ExtRewPrepMode
{
  OFF, USE, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, ExtRewPrepMode mode);
ExtRewPrepMode stringToExtRewPrepMode(const std::string& optarg);

enum class IandMode
{
  VALUE, SUM, BITWISE,
  __MAX_VALUE = BITWISE
};
std::ostream& operator<<(std::ostream& os, IandMode mode);
IandMode stringToIandMode(const std::string& optarg);

enum class InterpolantsMode
{
  DEFAULT, ASSUMPTIONS, CONJECTURE, SHARED, ALL,
  __MAX_VALUE = ALL
};
std::ostream& operator<<(std::ostream& os, InterpolantsMode mode);
InterpolantsMode stringToInterpolantsMode(const std::string& optarg);

enum class ModelCoresMode
{
  NONE, SIMPLE, NON_IMPLIED,
  __MAX_VALUE = NON_IMPLIED
};
std::ostream& operator<<(std::ostream& os, ModelCoresMode mode);
ModelCoresMode stringToModelCoresMode(const std::string& optarg);

enum class ProofMode
{
  OFF, PP_ONLY, SAT, FULL,
  __MAX_VALUE = FULL
};
std::ostream& operator<<(std::ostream& os, ProofMode mode);
ProofMode stringToProofMode(const std::string& optarg);

enum class SimplificationMode
{
  NONE, BATCH,
  __MAX_VALUE = BATCH
};
std::ostream& operator<<(std::ostream& os, SimplificationMode mode);
SimplificationMode stringToSimplificationMode(const std::string& optarg);

enum class SolveBVAsIntMode
{
  OFF, SUM, IAND, BV, BITWISE,
  __MAX_VALUE = BITWISE
};
std::ostream& operator<<(std::ostream& os, SolveBVAsIntMode mode);
SolveBVAsIntMode stringToSolveBVAsIntMode(const std::string& optarg);

enum class UnsatCoresMode
{
  OFF, SAT_PROOF, ASSUMPTIONS,
  __MAX_VALUE = ASSUMPTIONS
};
std::ostream& operator<<(std::ostream& os, UnsatCoresMode mode);
UnsatCoresMode stringToUnsatCoresMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderSMT
{
// clang-format off
  bool abstractValues = false;
  bool abstractValuesWasSetByUser = false;
  bool ackermann = false;
  bool ackermannWasSetByUser = false;
  bool bvToIntUsePow2 = false;
  bool bvToIntUsePow2WasSetByUser = false;
  uint64_t BVAndIntegerGranularity = 1;
  bool BVAndIntegerGranularityWasSetByUser = false;
  bool checkAbducts = false;
  bool checkAbductsWasSetByUser = false;
  bool checkInterpolants = false;
  bool checkInterpolantsWasSetByUser = false;
  bool checkModels = false;
  bool checkModelsWasSetByUser = false;
  bool checkProofs = false;
  bool checkProofsWasSetByUser = false;
  bool checkSynthSol = false;
  bool checkSynthSolWasSetByUser = false;
  bool checkUnsatCores = false;
  bool checkUnsatCoresWasSetByUser = false;
  bool debugCheckModels = false;
  bool debugCheckModelsWasSetByUser = false;
  DeepRestartMode deepRestartMode = DeepRestartMode::NONE;
  bool deepRestartModeWasSetByUser = false;
  double deepRestartFactor = 3.0;
  bool deepRestartFactorWasSetByUser = false;
  DifficultyMode difficultyMode = DifficultyMode::LEMMA_LITERAL_ALL;
  bool difficultyModeWasSetByUser = false;
  bool earlyIteRemoval = false;
  bool earlyIteRemovalWasSetByUser = false;
  ExtRewPrepMode extRewPrep = ExtRewPrepMode::OFF;
  bool extRewPrepWasSetByUser = false;
  bool foreignTheoryRewrite = false;
  bool foreignTheoryRewriteWasSetByUser = false;
  IandMode iandMode = IandMode::VALUE;
  bool iandModeWasSetByUser = false;
  InterpolantsMode interpolantsMode = InterpolantsMode::DEFAULT;
  bool interpolantsModeWasSetByUser = false;
  bool doITESimp = false;
  bool doITESimpWasSetByUser = false;
  bool learnedRewrite = false;
  bool learnedRewriteWasSetByUser = false;
  bool minimalUnsatCores = false;
  bool minimalUnsatCoresWasSetByUser = false;
  ModelCoresMode modelCoresMode = ModelCoresMode::NONE;
  bool modelCoresModeWasSetByUser = false;
  bool modelVarElimUneval = true;
  bool modelVarElimUnevalWasSetByUser = false;
  bool doITESimpOnRepeat = false;
  bool doITESimpOnRepeatWasSetByUser = false;
  bool printUnsatCoresFull = false;
  bool printUnsatCoresFullWasSetByUser = false;
  bool produceAbducts = false;
  bool produceAbductsWasSetByUser = false;
  bool produceAssertions = true;
  bool produceAssertionsWasSetByUser = false;
  bool produceAssignments = false;
  bool produceAssignmentsWasSetByUser = false;
  bool produceDifficulty = false;
  bool produceDifficultyWasSetByUser = false;
  bool produceInterpolants = false;
  bool produceInterpolantsWasSetByUser = false;
  bool produceLearnedLiterals = false;
  bool produceLearnedLiteralsWasSetByUser = false;
  bool produceModels = false;
  bool produceModelsWasSetByUser = false;
  bool produceProofs = false;
  bool produceProofsWasSetByUser = false;
  bool unsatAssumptions = false;
  bool unsatAssumptionsWasSetByUser = false;
  bool produceUnsatCores = false;
  bool produceUnsatCoresWasSetByUser = false;
  ProofMode proofMode = ProofMode::OFF;
  bool proofModeWasSetByUser = false;
  bool repeatSimp = false;
  bool repeatSimpWasSetByUser = false;
  bool compressItes = false;
  bool compressItesWasSetByUser = false;
  bool simplifyWithCareEnabled = false;
  bool simplifyWithCareEnabledWasSetByUser = false;
  SimplificationMode simplificationMode = SimplificationMode::BATCH;
  bool simplificationModeWasSetByUser = false;
  bool simplificationBoolConstProp = false;
  bool simplificationBoolConstPropWasSetByUser = false;
  SolveBVAsIntMode solveBVAsInt = SolveBVAsIntMode::OFF;
  bool solveBVAsIntWasSetByUser = false;
  uint64_t solveIntAsBV = 0;
  bool solveIntAsBVWasSetByUser = false;
  bool solveRealAsInt = false;
  bool solveRealAsIntWasSetByUser = false;
  bool sortInference = false;
  bool sortInferenceWasSetByUser = false;
  bool staticLearning = true;
  bool staticLearningWasSetByUser = false;
  bool unconstrainedSimp = false;
  bool unconstrainedSimpWasSetByUser = false;
  UnsatCoresMode unsatCoresMode = UnsatCoresMode::OFF;
  bool unsatCoresModeWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__SMT_H */
