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

#ifndef CVC5__OPTIONS__QUANTIFIERS_H
#define CVC5__OPTIONS__QUANTIFIERS_H

#include "options/options.h"

// clang-format off

// clang-format on

namespace cvc5::internal::options {

// clang-format off
enum class QcfMode
{
  CONFLICT_ONLY, PROP_EQ,
  __MAX_VALUE = PROP_EQ
};
std::ostream& operator<<(std::ostream& os, QcfMode mode);
QcfMode stringToQcfMode(const std::string& optarg);

enum class CegisSampleMode
{
  NONE, USE, TRUST,
  __MAX_VALUE = TRUST
};
std::ostream& operator<<(std::ostream& os, CegisSampleMode mode);
CegisSampleMode stringToCegisSampleMode(const std::string& optarg);

enum class CegqiBvIneqMode
{
  EQ_SLACK, EQ_BOUNDARY, KEEP,
  __MAX_VALUE = KEEP
};
std::ostream& operator<<(std::ostream& os, CegqiBvIneqMode mode);
CegqiBvIneqMode stringToCegqiBvIneqMode(const std::string& optarg);

enum class CondVarSplitQuantMode
{
  OFF, ON, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, CondVarSplitQuantMode mode);
CondVarSplitQuantMode stringToCondVarSplitQuantMode(const std::string& optarg);

enum class FmfMbqiMode
{
  NONE, FMC, TRUST,
  __MAX_VALUE = TRUST
};
std::ostream& operator<<(std::ostream& os, FmfMbqiMode mode);
FmfMbqiMode stringToFmfMbqiMode(const std::string& optarg);

enum class IevalMode
{
  OFF, USE, USE_LEARN,
  __MAX_VALUE = USE_LEARN
};
std::ostream& operator<<(std::ostream& os, IevalMode mode);
IevalMode stringToIevalMode(const std::string& optarg);

enum class InstWhenMode
{
  FULL, FULL_DELAY, FULL_LAST_CALL, FULL_DELAY_LAST_CALL, LAST_CALL,
  __MAX_VALUE = LAST_CALL
};
std::ostream& operator<<(std::ostream& os, InstWhenMode mode);
InstWhenMode stringToInstWhenMode(const std::string& optarg);

enum class IteLiftQuantMode
{
  NONE, SIMPLE, ALL,
  __MAX_VALUE = ALL
};
std::ostream& operator<<(std::ostream& os, IteLiftQuantMode mode);
IteLiftQuantMode stringToIteLiftQuantMode(const std::string& optarg);

enum class LiteralMatchMode
{
  NONE, USE, AGG_PREDICATE, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, LiteralMatchMode mode);
LiteralMatchMode stringToLiteralMatchMode(const std::string& optarg);

enum class MacrosQuantMode
{
  ALL, GROUND, GROUND_UF,
  __MAX_VALUE = GROUND_UF
};
std::ostream& operator<<(std::ostream& os, MacrosQuantMode mode);
MacrosQuantMode stringToMacrosQuantMode(const std::string& optarg);

enum class MiniscopeQuantMode
{
  OFF, CONJ, FV, CONJ_AND_FV, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, MiniscopeQuantMode mode);
MiniscopeQuantMode stringToMiniscopeQuantMode(const std::string& optarg);

enum class PreSkolemQuantMode
{
  OFF, ON, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, PreSkolemQuantMode mode);
PreSkolemQuantMode stringToPreSkolemQuantMode(const std::string& optarg);

enum class PrenexQuantMode
{
  NONE, SIMPLE, NORMAL,
  __MAX_VALUE = NORMAL
};
std::ostream& operator<<(std::ostream& os, PrenexQuantMode mode);
PrenexQuantMode stringToPrenexQuantMode(const std::string& optarg);

enum class PrintInstMode
{
  LIST, NUM,
  __MAX_VALUE = NUM
};
std::ostream& operator<<(std::ostream& os, PrintInstMode mode);
PrintInstMode stringToPrintInstMode(const std::string& optarg);

enum class QuantDSplitMode
{
  NONE, DEFAULT, AGG,
  __MAX_VALUE = AGG
};
std::ostream& operator<<(std::ostream& os, QuantDSplitMode mode);
QuantDSplitMode stringToQuantDSplitMode(const std::string& optarg);

enum class QuantRepMode
{
  EE, FIRST, DEPTH,
  __MAX_VALUE = DEPTH
};
std::ostream& operator<<(std::ostream& os, QuantRepMode mode);
QuantRepMode stringToQuantRepMode(const std::string& optarg);

enum class SygusEnumMode
{
  SMART, FAST, RANDOM, VAR_AGNOSTIC, AUTO,
  __MAX_VALUE = AUTO
};
std::ostream& operator<<(std::ostream& os, SygusEnumMode mode);
SygusEnumMode stringToSygusEnumMode(const std::string& optarg);

enum class SygusEvalUnfoldMode
{
  NONE, SINGLE, SINGLE_BOOL, MULTI,
  __MAX_VALUE = MULTI
};
std::ostream& operator<<(std::ostream& os, SygusEvalUnfoldMode mode);
SygusEvalUnfoldMode stringToSygusEvalUnfoldMode(const std::string& optarg);

enum class SygusFilterSolMode
{
  NONE, STRONG, WEAK,
  __MAX_VALUE = WEAK
};
std::ostream& operator<<(std::ostream& os, SygusFilterSolMode mode);
SygusFilterSolMode stringToSygusFilterSolMode(const std::string& optarg);

enum class SygusGrammarConsMode
{
  SIMPLE, ANY_CONST, ANY_TERM, ANY_TERM_CONCISE,
  __MAX_VALUE = ANY_TERM_CONCISE
};
std::ostream& operator<<(std::ostream& os, SygusGrammarConsMode mode);
SygusGrammarConsMode stringToSygusGrammarConsMode(const std::string& optarg);

enum class SygusInstMode
{
  PRIORITY_INST, PRIORITY_EVAL, INTERLEAVE,
  __MAX_VALUE = INTERLEAVE
};
std::ostream& operator<<(std::ostream& os, SygusInstMode mode);
SygusInstMode stringToSygusInstMode(const std::string& optarg);

enum class SygusInstScope
{
  IN, OUT, BOTH,
  __MAX_VALUE = BOTH
};
std::ostream& operator<<(std::ostream& os, SygusInstScope mode);
SygusInstScope stringToSygusInstScope(const std::string& optarg);

enum class SygusInstTermSelMode
{
  MIN, MAX, BOTH,
  __MAX_VALUE = BOTH
};
std::ostream& operator<<(std::ostream& os, SygusInstTermSelMode mode);
SygusInstTermSelMode stringToSygusInstTermSelMode(const std::string& optarg);

enum class SygusInvTemplMode
{
  NONE, PRE, POST,
  __MAX_VALUE = POST
};
std::ostream& operator<<(std::ostream& os, SygusInvTemplMode mode);
SygusInvTemplMode stringToSygusInvTemplMode(const std::string& optarg);

enum class SygusSolutionOutMode
{
  STATUS, STATUS_AND_DEF, STANDARD,
  __MAX_VALUE = STANDARD
};
std::ostream& operator<<(std::ostream& os, SygusSolutionOutMode mode);
SygusSolutionOutMode stringToSygusSolutionOutMode(const std::string& optarg);

enum class SygusQueryGenMode
{
  NONE, BASIC, SAMPLE_SAT, UNSAT,
  __MAX_VALUE = UNSAT
};
std::ostream& operator<<(std::ostream& os, SygusQueryGenMode mode);
SygusQueryGenMode stringToSygusQueryGenMode(const std::string& optarg);

enum class SygusQueryDumpFilesMode
{
  NONE, ALL, UNSOLVED,
  __MAX_VALUE = UNSOLVED
};
std::ostream& operator<<(std::ostream& os, SygusQueryDumpFilesMode mode);
SygusQueryDumpFilesMode stringToSygusQueryDumpFilesMode(const std::string& optarg);

enum class CegqiSingleInvMode
{
  NONE, USE, ALL,
  __MAX_VALUE = ALL
};
std::ostream& operator<<(std::ostream& os, CegqiSingleInvMode mode);
CegqiSingleInvMode stringToCegqiSingleInvMode(const std::string& optarg);

enum class CegqiSingleInvRconsMode
{
  NONE, TRY, ALL_LIMIT, ALL,
  __MAX_VALUE = ALL
};
std::ostream& operator<<(std::ostream& os, CegqiSingleInvRconsMode mode);
CegqiSingleInvRconsMode stringToCegqiSingleInvRconsMode(const std::string& optarg);

enum class SygusUnifPiMode
{
  NONE, COMPLETE, CENUM, CENUM_IGAIN,
  __MAX_VALUE = CENUM_IGAIN
};
std::ostream& operator<<(std::ostream& os, SygusUnifPiMode mode);
SygusUnifPiMode stringToSygusUnifPiMode(const std::string& optarg);

enum class TermDbMode
{
  ALL, RELEVANT,
  __MAX_VALUE = RELEVANT
};
std::ostream& operator<<(std::ostream& os, TermDbMode mode);
TermDbMode stringToTermDbMode(const std::string& optarg);

enum class TriggerActiveSelMode
{
  ALL, MIN, MAX,
  __MAX_VALUE = MAX
};
std::ostream& operator<<(std::ostream& os, TriggerActiveSelMode mode);
TriggerActiveSelMode stringToTriggerActiveSelMode(const std::string& optarg);

enum class TriggerSelMode
{
  MIN, MAX, MIN_SINGLE_MAX, MIN_SINGLE_ALL, ALL,
  __MAX_VALUE = ALL
};
std::ostream& operator<<(std::ostream& os, TriggerSelMode mode);
TriggerSelMode stringToTriggerSelMode(const std::string& optarg);

enum class UserPatMode
{
  USE, TRUST, STRICT, RESORT, IGNORE, INTERLEAVE,
  __MAX_VALUE = INTERLEAVE
};
std::ostream& operator<<(std::ostream& os, UserPatMode mode);
UserPatMode stringToUserPatMode(const std::string& optarg);

enum class UserPoolMode
{
  USE, TRUST, IGNORE,
  __MAX_VALUE = IGNORE
};
std::ostream& operator<<(std::ostream& os, UserPoolMode mode);
UserPoolMode stringToUserPoolMode(const std::string& optarg);

// clang-format on

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

struct HolderQUANTIFIERS
{
// clang-format off
  bool conflictBasedInst = true;
  bool conflictBasedInstWasSetByUser = false;
  bool cbqiAllConflict = false;
  bool cbqiAllConflictWasSetByUser = false;
  bool cbqiEagerCheckRd = true;
  bool cbqiEagerCheckRdWasSetByUser = false;
  bool cbqiEagerTest = true;
  bool cbqiEagerTestWasSetByUser = false;
  QcfMode cbqiMode = QcfMode::PROP_EQ;
  bool cbqiModeWasSetByUser = false;
  bool cbqiSkipRd = false;
  bool cbqiSkipRdWasSetByUser = false;
  bool cbqiTConstraint = false;
  bool cbqiTConstraintWasSetByUser = false;
  bool cbqiVoExp = false;
  bool cbqiVoExpWasSetByUser = false;
  CegisSampleMode cegisSample = CegisSampleMode::NONE;
  bool cegisSampleWasSetByUser = false;
  bool cegqi = false;
  bool cegqiWasSetByUser = false;
  bool cegqiAll = false;
  bool cegqiAllWasSetByUser = false;
  bool cegqiBv = true;
  bool cegqiBvWasSetByUser = false;
  bool cegqiBvConcInv = true;
  bool cegqiBvConcInvWasSetByUser = false;
  CegqiBvIneqMode cegqiBvIneqMode = CegqiBvIneqMode::EQ_BOUNDARY;
  bool cegqiBvIneqModeWasSetByUser = false;
  bool cegqiBvInterleaveValue = false;
  bool cegqiBvInterleaveValueWasSetByUser = false;
  bool cegqiBvLinearize = true;
  bool cegqiBvLinearizeWasSetByUser = false;
  bool cegqiBvRmExtract = true;
  bool cegqiBvRmExtractWasSetByUser = false;
  bool cegqiBvSolveNl = false;
  bool cegqiBvSolveNlWasSetByUser = false;
  bool cegqiFullEffort = false;
  bool cegqiFullEffortWasSetByUser = false;
  bool cegqiUseInfInt = false;
  bool cegqiUseInfIntWasSetByUser = false;
  bool cegqiUseInfReal = false;
  bool cegqiUseInfRealWasSetByUser = false;
  bool cegqiInnermost = true;
  bool cegqiInnermostWasSetByUser = false;
  bool cegqiMidpoint = false;
  bool cegqiMidpointWasSetByUser = false;
  bool cegqiMinBounds = false;
  bool cegqiMinBoundsWasSetByUser = false;
  bool cegqiMultiInst = false;
  bool cegqiMultiInstWasSetByUser = false;
  bool cegqiNestedQE = false;
  bool cegqiNestedQEWasSetByUser = false;
  bool cegqiNopt = true;
  bool cegqiNoptWasSetByUser = false;
  bool cegqiRoundUpLowerLia = false;
  bool cegqiRoundUpLowerLiaWasSetByUser = false;
  CondVarSplitQuantMode condVarSplitQuant = CondVarSplitQuantMode::ON;
  bool condVarSplitQuantWasSetByUser = false;
  bool conjectureGen = false;
  bool conjectureGenWasSetByUser = false;
  int64_t conjectureGenGtEnum = 50;
  bool conjectureGenGtEnumWasSetByUser = false;
  int64_t conjectureGenMaxDepth = 3;
  bool conjectureGenMaxDepthWasSetByUser = false;
  int64_t conjectureGenPerRound = 1;
  bool conjectureGenPerRoundWasSetByUser = false;
  bool consExpandTriggers = false;
  bool consExpandTriggersWasSetByUser = false;
  bool dtStcInduction = false;
  bool dtStcInductionWasSetByUser = false;
  bool dtVarExpandQuant = true;
  bool dtVarExpandQuantWasSetByUser = false;
  bool eMatching = true;
  bool eMatchingWasSetByUser = false;
  bool elimTautQuant = true;
  bool elimTautQuantWasSetByUser = false;
  bool enumInst = false;
  bool enumInstWasSetByUser = false;
  bool enumInstInterleave = false;
  bool enumInstInterleaveWasSetByUser = false;
  int64_t enumInstLimit = -1;
  bool enumInstLimitWasSetByUser = false;
  bool enumInstRd = true;
  bool enumInstRdWasSetByUser = false;
  bool enumInstStratify = false;
  bool enumInstStratifyWasSetByUser = false;
  bool enumInstSum = false;
  bool enumInstSumWasSetByUser = false;
  bool extRewriteQuant = false;
  bool extRewriteQuantWasSetByUser = false;
  bool finiteModelFind = false;
  bool finiteModelFindWasSetByUser = false;
  bool fmfBound = false;
  bool fmfBoundWasSetByUser = false;
  bool fmfBoundBlast = false;
  bool fmfBoundBlastWasSetByUser = false;
  bool fmfBoundLazy = false;
  bool fmfBoundLazyWasSetByUser = false;
  bool fmfFunWellDefined = false;
  bool fmfFunWellDefinedWasSetByUser = false;
  bool fmfFunWellDefinedRelevant = false;
  bool fmfFunWellDefinedRelevantWasSetByUser = false;
  FmfMbqiMode fmfMbqiMode = FmfMbqiMode::FMC;
  bool fmfMbqiModeWasSetByUser = false;
  int64_t fmfTypeCompletionThresh = 1000;
  bool fmfTypeCompletionThreshWasSetByUser = false;
  bool fullSaturateQuant = false;
  bool fullSaturateQuantWasSetByUser = false;
  bool globalNegate = false;
  bool globalNegateWasSetByUser = false;
  bool hoElim = false;
  bool hoElimWasSetByUser = false;
  bool hoElimStoreAx = true;
  bool hoElimStoreAxWasSetByUser = false;
  bool hoMatching = true;
  bool hoMatchingWasSetByUser = false;
  bool hoMergeTermDb = true;
  bool hoMergeTermDbWasSetByUser = false;
  IevalMode ievalMode = IevalMode::OFF;
  bool ievalModeWasSetByUser = false;
  bool incrementTriggers = true;
  bool incrementTriggersWasSetByUser = false;
  int64_t instMaxLevel = -1;
  bool instMaxLevelWasSetByUser = false;
  int64_t instMaxRounds = -1;
  bool instMaxRoundsWasSetByUser = false;
  bool instNoEntail = true;
  bool instNoEntailWasSetByUser = false;
  InstWhenMode instWhenMode = InstWhenMode::FULL_LAST_CALL;
  bool instWhenModeWasSetByUser = false;
  int64_t instWhenPhase = 2;
  bool instWhenPhaseWasSetByUser = false;
  bool intWfInduction = false;
  bool intWfInductionWasSetByUser = false;
  bool iteDtTesterSplitQuant = false;
  bool iteDtTesterSplitQuantWasSetByUser = false;
  IteLiftQuantMode iteLiftQuant = IteLiftQuantMode::SIMPLE;
  bool iteLiftQuantWasSetByUser = false;
  LiteralMatchMode literalMatchMode = LiteralMatchMode::USE;
  bool literalMatchModeWasSetByUser = false;
  bool macrosQuant = false;
  bool macrosQuantWasSetByUser = false;
  MacrosQuantMode macrosQuantMode = MacrosQuantMode::GROUND_UF;
  bool macrosQuantModeWasSetByUser = false;
  bool mbqi = false;
  bool mbqiWasSetByUser = false;
  bool mbqiInterleave = false;
  bool mbqiInterleaveWasSetByUser = false;
  bool fmfOneInstPerRound = false;
  bool fmfOneInstPerRoundWasSetByUser = false;
  MiniscopeQuantMode miniscopeQuant = MiniscopeQuantMode::CONJ_AND_FV;
  bool miniscopeQuantWasSetByUser = false;
  bool multiTriggerCache = false;
  bool multiTriggerCacheWasSetByUser = false;
  bool multiTriggerLinear = true;
  bool multiTriggerLinearWasSetByUser = false;
  bool multiTriggerPriority = false;
  bool multiTriggerPriorityWasSetByUser = false;
  bool multiTriggerWhenSingle = false;
  bool multiTriggerWhenSingleWasSetByUser = false;
  bool oracles = false;
  bool oraclesWasSetByUser = false;
  bool partialTriggers = false;
  bool partialTriggersWasSetByUser = false;
  bool poolInst = true;
  bool poolInstWasSetByUser = false;
  PreSkolemQuantMode preSkolemQuant = PreSkolemQuantMode::OFF;
  bool preSkolemQuantWasSetByUser = false;
  bool preSkolemQuantNested = true;
  bool preSkolemQuantNestedWasSetByUser = false;
  PrenexQuantMode prenexQuant = PrenexQuantMode::SIMPLE;
  bool prenexQuantWasSetByUser = false;
  bool prenexQuantUser = false;
  bool prenexQuantUserWasSetByUser = false;
  PrintInstMode printInstMode = PrintInstMode::LIST;
  bool printInstModeWasSetByUser = false;
  bool printInstFull = true;
  bool printInstFullWasSetByUser = false;
  bool purifyTriggers = false;
  bool purifyTriggersWasSetByUser = false;
  bool quantAlphaEquiv = true;
  bool quantAlphaEquivWasSetByUser = false;
  QuantDSplitMode quantDynamicSplit = QuantDSplitMode::DEFAULT;
  bool quantDynamicSplitWasSetByUser = false;
  bool quantFunWellDefined = false;
  bool quantFunWellDefinedWasSetByUser = false;
  bool quantInduction = false;
  bool quantInductionWasSetByUser = false;
  QuantRepMode quantRepMode = QuantRepMode::FIRST;
  bool quantRepModeWasSetByUser = false;
  bool registerQuantBodyTerms = false;
  bool registerQuantBodyTermsWasSetByUser = false;
  bool relationalTriggers = false;
  bool relationalTriggersWasSetByUser = false;
  bool relevantTriggers = false;
  bool relevantTriggersWasSetByUser = false;
  bool sygus = false;
  bool sygusWasSetByUser = false;
  bool sygusAddConstGrammar = true;
  bool sygusAddConstGrammarWasSetByUser = false;
  bool sygusArgRelevant = false;
  bool sygusArgRelevantWasSetByUser = false;
  bool sygusInvAutoUnfold = true;
  bool sygusInvAutoUnfoldWasSetByUser = false;
  bool sygusBoolIteReturnConst = true;
  bool sygusBoolIteReturnConstWasSetByUser = false;
  bool sygusCoreConnective = false;
  bool sygusCoreConnectiveWasSetByUser = false;
  bool sygusConstRepairAbort = false;
  bool sygusConstRepairAbortWasSetByUser = false;
  SygusEnumMode sygusEnumMode = SygusEnumMode::AUTO;
  bool sygusEnumModeWasSetByUser = false;
  uint64_t sygusEnumFastNumConsts = 5;
  bool sygusEnumFastNumConstsWasSetByUser = false;
  double sygusEnumRandomP = 0.5;
  bool sygusEnumRandomPWasSetByUser = false;
  SygusEvalUnfoldMode sygusEvalUnfoldMode = SygusEvalUnfoldMode::SINGLE_BOOL;
  bool sygusEvalUnfoldModeWasSetByUser = false;
  uint64_t sygusExprMinerCheckTimeout = 0;
  bool sygusExprMinerCheckTimeoutWasSetByUser = false;
  SygusFilterSolMode sygusFilterSolMode = SygusFilterSolMode::NONE;
  bool sygusFilterSolModeWasSetByUser = false;
  bool sygusFilterSolRevSubsume = false;
  bool sygusFilterSolRevSubsumeWasSetByUser = false;
  SygusGrammarConsMode sygusGrammarConsMode = SygusGrammarConsMode::SIMPLE;
  bool sygusGrammarConsModeWasSetByUser = false;
  bool sygusGrammarNorm = false;
  bool sygusGrammarNormWasSetByUser = false;
  bool sygusInference = false;
  bool sygusInferenceWasSetByUser = false;
  bool sygusInst = false;
  bool sygusInstWasSetByUser = false;
  SygusInstMode sygusInstMode = SygusInstMode::PRIORITY_INST;
  bool sygusInstModeWasSetByUser = false;
  SygusInstScope sygusInstScope = SygusInstScope::IN;
  bool sygusInstScopeWasSetByUser = false;
  SygusInstTermSelMode sygusInstTermSel = SygusInstTermSelMode::MIN;
  bool sygusInstTermSelWasSetByUser = false;
  SygusInvTemplMode sygusInvTemplMode = SygusInvTemplMode::POST;
  bool sygusInvTemplModeWasSetByUser = false;
  bool sygusInvTemplWhenSyntax = false;
  bool sygusInvTemplWhenSyntaxWasSetByUser = false;
  bool sygusMinGrammar = true;
  bool sygusMinGrammarWasSetByUser = false;
  SygusSolutionOutMode sygusOut = SygusSolutionOutMode::STANDARD;
  bool sygusOutWasSetByUser = false;
  bool sygusUnifPbe = true;
  bool sygusUnifPbeWasSetByUser = false;
  bool sygusPbeMultiFair = false;
  bool sygusPbeMultiFairWasSetByUser = false;
  int64_t sygusPbeMultiFairDiff = 0;
  bool sygusPbeMultiFairDiffWasSetByUser = false;
  bool sygusQePreproc = false;
  bool sygusQePreprocWasSetByUser = false;
  SygusQueryGenMode sygusQueryGen = SygusQueryGenMode::NONE;
  bool sygusQueryGenWasSetByUser = false;
  SygusQueryDumpFilesMode sygusQueryGenDumpFiles = SygusQueryDumpFilesMode::NONE;
  bool sygusQueryGenDumpFilesWasSetByUser = false;
  uint64_t sygusQueryGenThresh = 5;
  bool sygusQueryGenThreshWasSetByUser = false;
  bool sygusRecFun = true;
  bool sygusRecFunWasSetByUser = false;
  uint64_t sygusRecFunEvalLimit = 1000;
  bool sygusRecFunEvalLimitWasSetByUser = false;
  bool sygusRepairConst = false;
  bool sygusRepairConstWasSetByUser = false;
  uint64_t sygusRepairConstTimeout = 0;
  bool sygusRepairConstTimeoutWasSetByUser = false;
  bool sygusRewSynth = false;
  bool sygusRewSynthWasSetByUser = false;
  bool sygusRewSynthAccel = false;
  bool sygusRewSynthAccelWasSetByUser = false;
  bool sygusRewSynthCheck = true;
  bool sygusRewSynthCheckWasSetByUser = false;
  bool sygusRewSynthFilterCong = true;
  bool sygusRewSynthFilterCongWasSetByUser = false;
  bool sygusRewSynthFilterMatch = true;
  bool sygusRewSynthFilterMatchWasSetByUser = false;
  bool sygusRewSynthFilterNonLinear = false;
  bool sygusRewSynthFilterNonLinearWasSetByUser = false;
  bool sygusRewSynthFilterOrder = true;
  bool sygusRewSynthFilterOrderWasSetByUser = false;
  bool sygusRewSynthInput = false;
  bool sygusRewSynthInputWasSetByUser = false;
  int64_t sygusRewSynthInputNVars = 3;
  bool sygusRewSynthInputNVarsWasSetByUser = false;
  bool sygusRewSynthInputUseBool = false;
  bool sygusRewSynthInputUseBoolWasSetByUser = false;
  bool sygusRewSynthRec = false;
  bool sygusRewSynthRecWasSetByUser = false;
  bool sygusRewVerify = false;
  bool sygusRewVerifyWasSetByUser = false;
  bool sygusSampleFpUniform = false;
  bool sygusSampleFpUniformWasSetByUser = false;
  bool sygusSampleGrammar = true;
  bool sygusSampleGrammarWasSetByUser = false;
  int64_t sygusSamples = 1000;
  bool sygusSamplesWasSetByUser = false;
  CegqiSingleInvMode cegqiSingleInvMode = CegqiSingleInvMode::NONE;
  bool cegqiSingleInvModeWasSetByUser = false;
  bool cegqiSingleInvAbort = false;
  bool cegqiSingleInvAbortWasSetByUser = false;
  CegqiSingleInvRconsMode cegqiSingleInvReconstruct = CegqiSingleInvRconsMode::ALL;
  bool cegqiSingleInvReconstructWasSetByUser = false;
  int64_t cegqiSingleInvReconstructLimit = 10000;
  bool cegqiSingleInvReconstructLimitWasSetByUser = false;
  bool sygusStream = false;
  bool sygusStreamWasSetByUser = false;
  bool sygusUnifCondIndNoRepeatSol = true;
  bool sygusUnifCondIndNoRepeatSolWasSetByUser = false;
  SygusUnifPiMode sygusUnifPi = SygusUnifPiMode::NONE;
  bool sygusUnifPiWasSetByUser = false;
  bool sygusUnifShuffleCond = false;
  bool sygusUnifShuffleCondWasSetByUser = false;
  int64_t sygusVerifyInstMaxRounds = 10;
  bool sygusVerifyInstMaxRoundsWasSetByUser = false;
  uint64_t sygusVerifyTimeout = 0;
  bool sygusVerifyTimeoutWasSetByUser = false;
  bool termDbCd = true;
  bool termDbCdWasSetByUser = false;
  TermDbMode termDbMode = TermDbMode::ALL;
  bool termDbModeWasSetByUser = false;
  TriggerActiveSelMode triggerActiveSelMode = TriggerActiveSelMode::ALL;
  bool triggerActiveSelModeWasSetByUser = false;
  TriggerSelMode triggerSelMode = TriggerSelMode::MIN;
  bool triggerSelModeWasSetByUser = false;
  UserPatMode userPatternsQuant = UserPatMode::TRUST;
  bool userPatternsQuantWasSetByUser = false;
  UserPoolMode userPoolQuant = UserPoolMode::TRUST;
  bool userPoolQuantWasSetByUser = false;
  bool varElimQuant = true;
  bool varElimQuantWasSetByUser = false;
  bool varIneqElimQuant = true;
  bool varIneqElimQuantWasSetByUser = false;
// clang-format on
};

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT


}  // namespace cvc5::internal::options

#endif /* CVC5__OPTIONS__QUANTIFIERS_H */
