/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "base/check.h"
#include "base/output.h"
#include "options/io_utils.h"
#include "options/options.h"
#include "options/options_handler.h"
#include "options/options_listener.h"
#include "options/options_public.h"
#include "options/uf_options.h"

// clang-format off
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/builtin_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_options.h"
#include "options/expr_options.h"
#include "options/ff_options.h"
#include "options/fp_options.h"
#include "options/main_options.h"
#include "options/parallel_options.h"
#include "options/parser_options.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/prop_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/sets_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include <bitset>
#include <iostream>
#include "options/managed_streams.h"
#include "options/language.h"
#include <unordered_map>
// clang-format on

#include <cstring>
#include <iostream>
#include <limits>

namespace {
  // clang-format off
  enum class OptionEnum {
      ABSTRACT_VALUES,
      ACKERMANN,
      APPEND_LEARNED_LITERALS_TO_CUBES,
      APPROX_BRANCH_DEPTH,
      ARITH_BRAB,
      ARITH_EQ_SOLVER,
      ARITH_NO_PARTIAL_FUN,
      ARITH_PROP,
      ARITH_PROP_CLAUSES,
      ARITH_REWRITE_EQUALITIES,
      ARITH_STATIC_LEARNING,
      ARRAYS_EAGER_INDEX,
      ARRAYS_EAGER_LEMMAS,
      ARRAYS_EXP,
      ARRAYS_OPTIMIZE_LINEAR,
      ARRAYS_PROP,
      ARRAYS_REDUCE_SHARING,
      ARRAYS_WEAK_EQUIV,
      ASSIGN_FUNCTION_VALUES,
      BITBLAST,
      BITWISE_EQ,
      BOOL_TO_BV,
      BV_ASSERT_INPUT,
      BV_EAGER_EVAL,
      BV_GAUSS_ELIM,
      BV_INTRO_POW2,
      BV_PRINT_CONSTS_AS_INDEXED_SYMBOLS,
      BV_PROPAGATE,
      BV_RW_EXTEND_EQ,
      BV_SAT_SOLVER,
      BV_SOLVER,
      BV_TO_BOOL,
      BV_TO_INT_USE_POW2,
      BVAND_INTEGER_GRANULARITY,
      CBQI,
      CBQI_ALL_CONFLICT,
      CBQI_EAGER_CHECK_RD,
      CBQI_EAGER_TEST,
      CBQI_MODE,
      CBQI_SKIP_RD,
      CBQI_TCONSTRAINT,
      CBQI_VO_EXP,
      CDT_BISIMILAR,
      CEGIS_SAMPLE,
      CEGQI,
      CEGQI_ALL,
      CEGQI_BV,
      CEGQI_BV_CONCAT_INV,
      CEGQI_BV_INEQ,
      CEGQI_BV_INTERLEAVE_VALUE,
      CEGQI_BV_LINEAR,
      CEGQI_BV_RM_EXTRACT,
      CEGQI_BV_SOLVE_NL,
      CEGQI_FULL,
      CEGQI_INF_INT,
      CEGQI_INF_REAL,
      CEGQI_INNERMOST,
      CEGQI_MIDPOINT,
      CEGQI_MIN_BOUNDS,
      CEGQI_MULTI_INST,
      CEGQI_NESTED_QE,
      CEGQI_NOPT,
      CEGQI_ROUND_UP_LIA,
      CHECK_ABDUCTS,
      CHECK_INTERPOLANTS,
      CHECK_MODELS,
      CHECK_PROOF_STEPS,
      CHECK_PROOFS,
      CHECK_SYNTH_SOL,
      CHECK_UNSAT_CORES,
      CHECKS_BEFORE_PARTITION,
      CHECKS_BETWEEN_PARTITIONS,
      COLLECT_PIVOT_STATS,
      COMPUTE_PARTITIONS,
      COND_VAR_SPLIT_QUANT,
      CONDENSE_FUNCTION_VALUES,
      CONJECTURE_GEN,
      CONJECTURE_GEN_GT_ENUM,
      CONJECTURE_GEN_MAX_DEPTH,
      CONJECTURE_GEN_PER_ROUND,
      CONS_EXP_TRIGGERS,
      COPYRIGHT,
      CUT_ALL_BOUNDED,
      DAG_THRESH,
      DEBUG_CHECK_MODELS,
      DECISION,
      DEEP_RESTART,
      DEEP_RESTART_FACTOR,
      DIFFICULTY_MODE,
      DIO_DECOMPS,
      DIO_SOLVER,
      DIO_TURNS,
      DT_BINARY_SPLIT,
      DT_BLAST_SPLITS,
      DT_CYCLIC,
      DT_INFER_AS_LEMMAS,
      DT_NESTED_REC,
      DT_POLITE_OPTIMIZE,
      DT_SHARE_SEL,
      DT_STC_IND,
      DT_VAR_EXP_QUANT,
      DUMP_DIFFICULTY,
      DUMP_INSTANTIATIONS,
      DUMP_INSTANTIATIONS_DEBUG,
      DUMP_MODELS,
      DUMP_PROOFS,
      DUMP_UNSAT_CORES,
      E_MATCHING,
      EAGER_ARITH_BV_CONV,
      EARLY_EXIT,
      EARLY_ITE_REMOVAL,
      EE_MODE,
      ELIM_TAUT_QUANT,
      ENUM_INST,
      ENUM_INST_INTERLEAVE,
      ENUM_INST_LIMIT,
      ENUM_INST_RD,
      ENUM_INST_STRATIFY,
      ENUM_INST_SUM,
      ERR,
      ERROR_SELECTION_RULE,
      EXPR_DEPTH,
      EXT_REW_PREP,
      EXT_REWRITE_QUANT,
      FC_PENALTIES,
      FF_FIELD_POLYS,
      FF_TRACE_GB,
      FILENAME,
      FILESYSTEM_ACCESS,
      FINITE_MODEL_FIND,
      FLATTEN_HO_CHAINS,
      FLEX_PARSER,
      FMF_BOUND,
      FMF_BOUND_BLAST,
      FMF_BOUND_LAZY,
      FMF_FUN,
      FMF_FUN_RLV,
      FMF_MBQI,
      FMF_TYPE_COMPLETION_THRESH,
      FORCE_LOGIC,
      FORCE_NO_LIMIT_CPU_WHILE_DUMP,
      FOREIGN_THEORY_REWRITE,
      FP_EXP,
      FP_LAZY_WB,
      FULL_SATURATE_QUANT,
      GLOBAL_DECLARATIONS,
      GLOBAL_NEGATE,
      HELP,
      HEURISTIC_PIVOTS,
      HO_ELIM,
      HO_ELIM_STORE_AX,
      HO_MATCHING,
      HO_MERGE_TERM_DB,
      IAND_MODE,
      IEVAL,
      IN,
      INCREMENT_TRIGGERS,
      INCREMENTAL,
      INST_MAX_LEVEL,
      INST_MAX_ROUNDS,
      INST_NO_ENTAIL,
      INST_WHEN,
      INST_WHEN_PHASE,
      INT_WF_IND,
      INTERACTIVE,
      INTERPOLANTS_MODE,
      ITE_DTT_SPLIT_QUANT,
      ITE_LIFT_QUANT,
      ITE_SIMP,
      JH_RLV_ORDER,
      JH_SKOLEM,
      JH_SKOLEM_RLV,
      LANG,
      LEARNED_REWRITE,
      LEMMAS_ON_REPLAY_FAILURE,
      LFSC_EXPAND_TRUST,
      LFSC_FLATTEN,
      LITERAL_MATCHING,
      MACROS_QUANT,
      MACROS_QUANT_MODE,
      MAXCUTSINCONTEXT,
      MBQI,
      MBQI_INTERLEAVE,
      MBQI_ONE_INST_PER_ROUND,
      MINIMAL_UNSAT_CORES,
      MINISAT_DUMP_DIMACS,
      MINISAT_SIMPLIFICATION,
      MINISCOPE_QUANT,
      MIPLIB_TRICK,
      MIPLIB_TRICK_SUBS,
      MODEL_CORES,
      MODEL_U_PRINT,
      MODEL_VAR_ELIM_UNEVAL,
      MULTI_TRIGGER_CACHE,
      MULTI_TRIGGER_LINEAR,
      MULTI_TRIGGER_PRIORITY,
      MULTI_TRIGGER_WHEN_SINGLE,
      NEW_PROP,
      NL_COV,
      NL_COV_FORCE,
      NL_COV_LIFT,
      NL_COV_LINEAR_MODEL,
      NL_COV_PROJ,
      NL_COV_PRUNE,
      NL_COV_VAR_ELIM,
      NL_EXT,
      NL_EXT_ENT_CONF,
      NL_EXT_FACTOR,
      NL_EXT_INC_PREC,
      NL_EXT_PURIFY,
      NL_EXT_RBOUND,
      NL_EXT_REWRITE,
      NL_EXT_SPLIT_ZERO,
      NL_EXT_TF_TAYLOR_DEG,
      NL_EXT_TF_TPLANES,
      NL_EXT_TPLANES,
      NL_EXT_TPLANES_INTERLEAVE,
      NL_ICP,
      NL_RLV,
      NL_RLV_ASSERT_BOUNDS,
      ON_REPEAT_ITE_SIMP,
      OPT_RES_RECONSTRUCTION_SIZE,
      ORACLES,
      OUT,
      OUTPUT,
      OUTPUT_LANG,
      PARSE_ONLY,
      PARTIAL_TRIGGERS,
      PARTITION_CHECK,
      PARTITION_CONFLICT_SIZE,
      PARTITION_STRATEGY,
      PB_REWRITES,
      PIVOT_THRESHOLD,
      POOL_INST,
      PORTFOLIO_JOBS,
      PP_ASSERT_MAX_SUB_SIZE,
      PRE_SKOLEM_QUANT,
      PRE_SKOLEM_QUANT_NESTED,
      PRENEX_QUANT,
      PRENEX_QUANT_USER,
      PREPROCESS_ONLY,
      PREREGISTER_MODE,
      PRINT_DOT_CLUSTERS,
      PRINT_INST,
      PRINT_INST_FULL,
      PRINT_SUCCESS,
      PRINT_UNSAT_CORES_FULL,
      PRODUCE_ABDUCTS,
      PRODUCE_ASSERTIONS,
      PRODUCE_ASSIGNMENTS,
      PRODUCE_DIFFICULTY,
      PRODUCE_INTERPOLANTS,
      PRODUCE_LEARNED_LITERALS,
      PRODUCE_MODELS,
      PRODUCE_PROOFS,
      PRODUCE_UNSAT_ASSUMPTIONS,
      PRODUCE_UNSAT_CORES,
      PROOF_ALETHE_RES_PIVOTS,
      PROOF_ANNOTATE,
      PROOF_CHECK,
      PROOF_DOT_DAG,
      PROOF_FORMAT_MODE,
      PROOF_GRANULARITY,
      PROOF_MODE,
      PROOF_PEDANTIC,
      PROOF_PP_MERGE,
      PROOF_PRINT_CONCLUSION,
      PROOF_PRUNE_INPUT,
      PROOF_REWRITE_RCONS_LIMIT,
      PROP_ROW_LENGTH,
      PURIFY_TRIGGERS,
      QUANT_ALPHA_EQUIV,
      QUANT_DSPLIT,
      QUANT_FUN_WD,
      QUANT_IND,
      QUANT_REP_MODE,
      QUIET,
      RANDOM_FREQ,
      RE_ELIM,
      RE_INTER_MODE,
      REGISTER_QUANT_BODY_TERMS,
      RELATIONAL_TRIGGERS,
      RELEVANCE_FILTER,
      RELEVANT_TRIGGERS,
      REPEAT_SIMP,
      REPLAY_EARLY_CLOSE_DEPTH,
      REPLAY_LEMMA_REJECT_CUT,
      REPLAY_NUM_ERR_PENALTY,
      REPLAY_REJECT_CUT,
      RESTART_INT_BASE,
      RESTART_INT_INC,
      RESTRICT_PIVOTS,
      REVERT_ARITH_MODELS_ON_UNSAT,
      RLIMIT,
      RLIMIT_PER,
      RR_TURNS,
      RWEIGHT,
      SAT_RANDOM_SEED,
      SE_SOLVE_INT,
      SEED,
      SEGV_SPIN,
      SEMANTIC_CHECKS,
      SEP_MIN_REFINE,
      SEP_PRE_SKOLEM_EMP,
      SEQ_ARRAY,
      SETS_EXT,
      SETS_INFER_AS_LEMMAS,
      SETS_PROXY_LEMMAS,
      SHOW_CONFIG,
      SHOW_TRACE_TAGS,
      SIMP_ITE_COMPRESS,
      SIMP_WITH_CARE,
      SIMPLEX_CHECK_PERIOD,
      SIMPLIFICATION,
      SIMPLIFICATION_BCP,
      SOI_QE,
      SOLVE_BV_AS_INT,
      SOLVE_INT_AS_BV,
      SOLVE_REAL_AS_INT,
      SORT_INFERENCE,
      STANDARD_EFFORT_VARIABLE_ORDER_PIVOTS,
      STATIC_LEARNING,
      STATS,
      STATS_ALL,
      STATS_EVERY_QUERY,
      STATS_INTERNAL,
      STDIN_INPUT_PER_LINE,
      STRICT_PARSING,
      STRINGS_ALPHA_CARD,
      STRINGS_CHECK_ENTAIL_LEN,
      STRINGS_CODE_ELIM,
      STRINGS_DEQ_EXT,
      STRINGS_EAGER_EVAL,
      STRINGS_EAGER_LEN_RE,
      STRINGS_EAGER_REG,
      STRINGS_EAGER_SOLVER,
      STRINGS_EXP,
      STRINGS_FF,
      STRINGS_FMF,
      STRINGS_INFER_AS_LEMMAS,
      STRINGS_INFER_SYM,
      STRINGS_LAZY_PP,
      STRINGS_LEN_NORM,
      STRINGS_MBR,
      STRINGS_MODEL_MAX_LEN,
      STRINGS_PROCESS_LOOP_MODE,
      STRINGS_RE_POSC_EAGER,
      STRINGS_REGEXP_INCLUSION,
      STRINGS_REXPLAIN_LEMMAS,
      SYGUS,
      SYGUS_ABORT_SIZE,
      SYGUS_ADD_CONST_GRAMMAR,
      SYGUS_ARG_RELEVANT,
      SYGUS_AUTO_UNFOLD,
      SYGUS_BOOL_ITE_RETURN_CONST,
      SYGUS_CORE_CONNECTIVE,
      SYGUS_CREPAIR_ABORT,
      SYGUS_ENUM,
      SYGUS_ENUM_FAST_NUM_CONSTS,
      SYGUS_ENUM_RANDOM_P,
      SYGUS_EVAL_UNFOLD,
      SYGUS_EXPR_MINER_CHECK_TIMEOUT,
      SYGUS_FAIR,
      SYGUS_FAIR_MAX,
      SYGUS_FILTER_SOL,
      SYGUS_FILTER_SOL_REV,
      SYGUS_GRAMMAR_CONS,
      SYGUS_GRAMMAR_NORM,
      SYGUS_INFERENCE,
      SYGUS_INST,
      SYGUS_INST_MODE,
      SYGUS_INST_SCOPE,
      SYGUS_INST_TERM_SEL,
      SYGUS_INV_TEMPL,
      SYGUS_INV_TEMPL_WHEN_SG,
      SYGUS_MIN_GRAMMAR,
      SYGUS_OUT,
      SYGUS_PBE,
      SYGUS_PBE_MULTI_FAIR,
      SYGUS_PBE_MULTI_FAIR_DIFF,
      SYGUS_QE_PREPROC,
      SYGUS_QUERY_GEN,
      SYGUS_QUERY_GEN_DUMP_FILES,
      SYGUS_QUERY_GEN_THRESH,
      SYGUS_REC_FUN,
      SYGUS_REC_FUN_EVAL_LIMIT,
      SYGUS_REPAIR_CONST,
      SYGUS_REPAIR_CONST_TIMEOUT,
      SYGUS_REWRITER,
      SYGUS_RR_SYNTH,
      SYGUS_RR_SYNTH_ACCEL,
      SYGUS_RR_SYNTH_CHECK,
      SYGUS_RR_SYNTH_FILTER_CONG,
      SYGUS_RR_SYNTH_FILTER_MATCH,
      SYGUS_RR_SYNTH_FILTER_NL,
      SYGUS_RR_SYNTH_FILTER_ORDER,
      SYGUS_RR_SYNTH_INPUT,
      SYGUS_RR_SYNTH_INPUT_NVARS,
      SYGUS_RR_SYNTH_INPUT_USE_BOOL,
      SYGUS_RR_SYNTH_REC,
      SYGUS_RR_VERIFY,
      SYGUS_SAMPLE_FP_UNIFORM,
      SYGUS_SAMPLE_GRAMMAR,
      SYGUS_SAMPLES,
      SYGUS_SI,
      SYGUS_SI_ABORT,
      SYGUS_SI_RCONS,
      SYGUS_SI_RCONS_LIMIT,
      SYGUS_SIMPLE_SYM_BREAK,
      SYGUS_STREAM,
      SYGUS_SYM_BREAK_LAZY,
      SYGUS_SYM_BREAK_PBE,
      SYGUS_SYM_BREAK_RLV,
      SYGUS_UNIF_COND_INDEPENDENT_NO_REPEAT_SOL,
      SYGUS_UNIF_PI,
      SYGUS_UNIF_SHUFFLE_COND,
      SYGUS_VERIFY_INST_MAX_ROUNDS,
      SYGUS_VERIFY_TIMEOUT,
      SYMMETRY_BREAKER,
      TC_MODE,
      TERM_DB_CD,
      TERM_DB_MODE,
      THEORYOF_MODE,
      TLIMIT,
      TLIMIT_PER,
      TRACE,
      TRIGGER_ACTIVE_SEL,
      TRIGGER_SEL,
      TYPE_CHECKING,
      UF_HO_EXT,
      UF_LAZY_LL,
      UF_SS,
      UF_SS_ABORT_CARD,
      UF_SS_FAIR,
      UF_SS_FAIR_MONOTONE,
      UNATE_LEMMAS,
      UNCONSTRAINED_SIMP,
      UNSAT_CORES_MODE,
      USE_APPROX,
      USE_FCSIMPLEX,
      USE_PORTFOLIO,
      USE_SOI,
      USER_PAT,
      USER_POOL,
      VAR_ELIM_QUANT,
      VAR_INEQ_ELIM_QUANT,
      VERBOSE,
      VERBOSITY,
      VERSION,
      WF_CHECKING,
      WRITE_PARTITIONS_TO,
    };
    const std::unordered_map<std::string, OptionEnum> NAME_TO_ENUM = {
      { "abstract-values", OptionEnum::ABSTRACT_VALUES },
      { "ackermann", OptionEnum::ACKERMANN },
      { "append-learned-literals-to-cubes", OptionEnum::APPEND_LEARNED_LITERALS_TO_CUBES },
      { "approx-branch-depth", OptionEnum::APPROX_BRANCH_DEPTH },
      { "arith-brab", OptionEnum::ARITH_BRAB },
      { "arith-eq-solver", OptionEnum::ARITH_EQ_SOLVER },
      { "arith-no-partial-fun", OptionEnum::ARITH_NO_PARTIAL_FUN },
      { "arith-prop", OptionEnum::ARITH_PROP },
      { "arith-prop-clauses", OptionEnum::ARITH_PROP_CLAUSES },
      { "arith-rewrite-equalities", OptionEnum::ARITH_REWRITE_EQUALITIES },
      { "arith-static-learning", OptionEnum::ARITH_STATIC_LEARNING },
      { "arrays-eager-index", OptionEnum::ARRAYS_EAGER_INDEX },
      { "arrays-eager-lemmas", OptionEnum::ARRAYS_EAGER_LEMMAS },
      { "arrays-exp", OptionEnum::ARRAYS_EXP },
      { "arrays-optimize-linear", OptionEnum::ARRAYS_OPTIMIZE_LINEAR },
      { "arrays-prop", OptionEnum::ARRAYS_PROP },
      { "arrays-reduce-sharing", OptionEnum::ARRAYS_REDUCE_SHARING },
      { "arrays-weak-equiv", OptionEnum::ARRAYS_WEAK_EQUIV },
      { "assign-function-values", OptionEnum::ASSIGN_FUNCTION_VALUES },
      { "bitblast", OptionEnum::BITBLAST },
      { "bitwise-eq", OptionEnum::BITWISE_EQ },
      { "bool-to-bv", OptionEnum::BOOL_TO_BV },
      { "bv-assert-input", OptionEnum::BV_ASSERT_INPUT },
      { "bv-eager-eval", OptionEnum::BV_EAGER_EVAL },
      { "bv-gauss-elim", OptionEnum::BV_GAUSS_ELIM },
      { "bv-intro-pow2", OptionEnum::BV_INTRO_POW2 },
      { "bv-print-consts-as-indexed-symbols", OptionEnum::BV_PRINT_CONSTS_AS_INDEXED_SYMBOLS },
      { "bv-propagate", OptionEnum::BV_PROPAGATE },
      { "bv-rw-extend-eq", OptionEnum::BV_RW_EXTEND_EQ },
      { "bv-sat-solver", OptionEnum::BV_SAT_SOLVER },
      { "bv-solver", OptionEnum::BV_SOLVER },
      { "bv-to-bool", OptionEnum::BV_TO_BOOL },
      { "bv-to-int-use-pow2", OptionEnum::BV_TO_INT_USE_POW2 },
      { "bvand-integer-granularity", OptionEnum::BVAND_INTEGER_GRANULARITY },
      { "cbqi", OptionEnum::CBQI },
      { "cbqi-all-conflict", OptionEnum::CBQI_ALL_CONFLICT },
      { "cbqi-eager-check-rd", OptionEnum::CBQI_EAGER_CHECK_RD },
      { "cbqi-eager-test", OptionEnum::CBQI_EAGER_TEST },
      { "cbqi-mode", OptionEnum::CBQI_MODE },
      { "cbqi-skip-rd", OptionEnum::CBQI_SKIP_RD },
      { "cbqi-tconstraint", OptionEnum::CBQI_TCONSTRAINT },
      { "cbqi-vo-exp", OptionEnum::CBQI_VO_EXP },
      { "cdt-bisimilar", OptionEnum::CDT_BISIMILAR },
      { "cegis-sample", OptionEnum::CEGIS_SAMPLE },
      { "cegqi", OptionEnum::CEGQI },
      { "cegqi-all", OptionEnum::CEGQI_ALL },
      { "cegqi-bv", OptionEnum::CEGQI_BV },
      { "cegqi-bv-concat-inv", OptionEnum::CEGQI_BV_CONCAT_INV },
      { "cegqi-bv-ineq", OptionEnum::CEGQI_BV_INEQ },
      { "cegqi-bv-interleave-value", OptionEnum::CEGQI_BV_INTERLEAVE_VALUE },
      { "cegqi-bv-linear", OptionEnum::CEGQI_BV_LINEAR },
      { "cegqi-bv-rm-extract", OptionEnum::CEGQI_BV_RM_EXTRACT },
      { "cegqi-bv-solve-nl", OptionEnum::CEGQI_BV_SOLVE_NL },
      { "cegqi-full", OptionEnum::CEGQI_FULL },
      { "cegqi-inf-int", OptionEnum::CEGQI_INF_INT },
      { "cegqi-inf-real", OptionEnum::CEGQI_INF_REAL },
      { "cegqi-innermost", OptionEnum::CEGQI_INNERMOST },
      { "cegqi-midpoint", OptionEnum::CEGQI_MIDPOINT },
      { "cegqi-min-bounds", OptionEnum::CEGQI_MIN_BOUNDS },
      { "cegqi-multi-inst", OptionEnum::CEGQI_MULTI_INST },
      { "cegqi-nested-qe", OptionEnum::CEGQI_NESTED_QE },
      { "cegqi-nopt", OptionEnum::CEGQI_NOPT },
      { "cegqi-round-up-lia", OptionEnum::CEGQI_ROUND_UP_LIA },
      { "check-abducts", OptionEnum::CHECK_ABDUCTS },
      { "check-interpolants", OptionEnum::CHECK_INTERPOLANTS },
      { "check-models", OptionEnum::CHECK_MODELS },
      { "check-proof-steps", OptionEnum::CHECK_PROOF_STEPS },
      { "check-proofs", OptionEnum::CHECK_PROOFS },
      { "check-synth-sol", OptionEnum::CHECK_SYNTH_SOL },
      { "check-unsat-cores", OptionEnum::CHECK_UNSAT_CORES },
      { "checks-before-partition", OptionEnum::CHECKS_BEFORE_PARTITION },
      { "checks-between-partitions", OptionEnum::CHECKS_BETWEEN_PARTITIONS },
      { "collect-pivot-stats", OptionEnum::COLLECT_PIVOT_STATS },
      { "compute-partitions", OptionEnum::COMPUTE_PARTITIONS },
      { "cond-var-split-quant", OptionEnum::COND_VAR_SPLIT_QUANT },
      { "condense-function-values", OptionEnum::CONDENSE_FUNCTION_VALUES },
      { "conjecture-gen", OptionEnum::CONJECTURE_GEN },
      { "conjecture-gen-gt-enum", OptionEnum::CONJECTURE_GEN_GT_ENUM },
      { "conjecture-gen-max-depth", OptionEnum::CONJECTURE_GEN_MAX_DEPTH },
      { "conjecture-gen-per-round", OptionEnum::CONJECTURE_GEN_PER_ROUND },
      { "cons-exp-triggers", OptionEnum::CONS_EXP_TRIGGERS },
      { "copyright", OptionEnum::COPYRIGHT },
      { "cut-all-bounded", OptionEnum::CUT_ALL_BOUNDED },
      { "dag-thresh", OptionEnum::DAG_THRESH },
      { "debug-check-models", OptionEnum::DEBUG_CHECK_MODELS },
      { "decision", OptionEnum::DECISION },
      { "decision-mode", OptionEnum::DECISION },
      { "deep-restart", OptionEnum::DEEP_RESTART },
      { "deep-restart-factor", OptionEnum::DEEP_RESTART_FACTOR },
      { "difficulty-mode", OptionEnum::DIFFICULTY_MODE },
      { "dio-decomps", OptionEnum::DIO_DECOMPS },
      { "dio-solver", OptionEnum::DIO_SOLVER },
      { "dio-turns", OptionEnum::DIO_TURNS },
      { "dt-binary-split", OptionEnum::DT_BINARY_SPLIT },
      { "dt-blast-splits", OptionEnum::DT_BLAST_SPLITS },
      { "dt-cyclic", OptionEnum::DT_CYCLIC },
      { "dt-infer-as-lemmas", OptionEnum::DT_INFER_AS_LEMMAS },
      { "dt-nested-rec", OptionEnum::DT_NESTED_REC },
      { "dt-polite-optimize", OptionEnum::DT_POLITE_OPTIMIZE },
      { "dt-share-sel", OptionEnum::DT_SHARE_SEL },
      { "dt-stc-ind", OptionEnum::DT_STC_IND },
      { "dt-var-exp-quant", OptionEnum::DT_VAR_EXP_QUANT },
      { "dump-difficulty", OptionEnum::DUMP_DIFFICULTY },
      { "dump-instantiations", OptionEnum::DUMP_INSTANTIATIONS },
      { "dump-instantiations-debug", OptionEnum::DUMP_INSTANTIATIONS_DEBUG },
      { "dump-models", OptionEnum::DUMP_MODELS },
      { "dump-proofs", OptionEnum::DUMP_PROOFS },
      { "dump-unsat-cores", OptionEnum::DUMP_UNSAT_CORES },
      { "e-matching", OptionEnum::E_MATCHING },
      { "eager-arith-bv-conv", OptionEnum::EAGER_ARITH_BV_CONV },
      { "early-exit", OptionEnum::EARLY_EXIT },
      { "early-ite-removal", OptionEnum::EARLY_ITE_REMOVAL },
      { "ee-mode", OptionEnum::EE_MODE },
      { "elim-taut-quant", OptionEnum::ELIM_TAUT_QUANT },
      { "enum-inst", OptionEnum::ENUM_INST },
      { "enum-inst-interleave", OptionEnum::ENUM_INST_INTERLEAVE },
      { "enum-inst-limit", OptionEnum::ENUM_INST_LIMIT },
      { "enum-inst-rd", OptionEnum::ENUM_INST_RD },
      { "enum-inst-stratify", OptionEnum::ENUM_INST_STRATIFY },
      { "enum-inst-sum", OptionEnum::ENUM_INST_SUM },
      { "diagnostic-output-channel", OptionEnum::ERR },
      { "err", OptionEnum::ERR },
      { "error-selection-rule", OptionEnum::ERROR_SELECTION_RULE },
      { "expr-depth", OptionEnum::EXPR_DEPTH },
      { "ext-rew-prep", OptionEnum::EXT_REW_PREP },
      { "ext-rewrite-quant", OptionEnum::EXT_REWRITE_QUANT },
      { "fc-penalties", OptionEnum::FC_PENALTIES },
      { "ff-field-polys", OptionEnum::FF_FIELD_POLYS },
      { "ff-trace-gb", OptionEnum::FF_TRACE_GB },
      { "filename", OptionEnum::FILENAME },
      { "filesystem-access", OptionEnum::FILESYSTEM_ACCESS },
      { "finite-model-find", OptionEnum::FINITE_MODEL_FIND },
      { "flatten-ho-chains", OptionEnum::FLATTEN_HO_CHAINS },
      { "flex-parser", OptionEnum::FLEX_PARSER },
      { "fmf-bound", OptionEnum::FMF_BOUND },
      { "fmf-bound-blast", OptionEnum::FMF_BOUND_BLAST },
      { "fmf-bound-lazy", OptionEnum::FMF_BOUND_LAZY },
      { "fmf-fun", OptionEnum::FMF_FUN },
      { "fmf-fun-rlv", OptionEnum::FMF_FUN_RLV },
      { "fmf-mbqi", OptionEnum::FMF_MBQI },
      { "fmf-type-completion-thresh", OptionEnum::FMF_TYPE_COMPLETION_THRESH },
      { "force-logic", OptionEnum::FORCE_LOGIC },
      { "force-no-limit-cpu-while-dump", OptionEnum::FORCE_NO_LIMIT_CPU_WHILE_DUMP },
      { "foreign-theory-rewrite", OptionEnum::FOREIGN_THEORY_REWRITE },
      { "fp-exp", OptionEnum::FP_EXP },
      { "fp-lazy-wb", OptionEnum::FP_LAZY_WB },
      { "full-saturate-quant", OptionEnum::FULL_SATURATE_QUANT },
      { "global-declarations", OptionEnum::GLOBAL_DECLARATIONS },
      { "global-negate", OptionEnum::GLOBAL_NEGATE },
      { "help", OptionEnum::HELP },
      { "heuristic-pivots", OptionEnum::HEURISTIC_PIVOTS },
      { "ho-elim", OptionEnum::HO_ELIM },
      { "ho-elim-store-ax", OptionEnum::HO_ELIM_STORE_AX },
      { "ho-matching", OptionEnum::HO_MATCHING },
      { "ho-merge-term-db", OptionEnum::HO_MERGE_TERM_DB },
      { "iand-mode", OptionEnum::IAND_MODE },
      { "ieval", OptionEnum::IEVAL },
      { "in", OptionEnum::IN },
      { "increment-triggers", OptionEnum::INCREMENT_TRIGGERS },
      { "incremental", OptionEnum::INCREMENTAL },
      { "inst-max-level", OptionEnum::INST_MAX_LEVEL },
      { "inst-max-rounds", OptionEnum::INST_MAX_ROUNDS },
      { "inst-no-entail", OptionEnum::INST_NO_ENTAIL },
      { "inst-when", OptionEnum::INST_WHEN },
      { "inst-when-phase", OptionEnum::INST_WHEN_PHASE },
      { "int-wf-ind", OptionEnum::INT_WF_IND },
      { "interactive", OptionEnum::INTERACTIVE },
      { "interpolants-mode", OptionEnum::INTERPOLANTS_MODE },
      { "ite-dtt-split-quant", OptionEnum::ITE_DTT_SPLIT_QUANT },
      { "ite-lift-quant", OptionEnum::ITE_LIFT_QUANT },
      { "ite-simp", OptionEnum::ITE_SIMP },
      { "jh-rlv-order", OptionEnum::JH_RLV_ORDER },
      { "jh-skolem", OptionEnum::JH_SKOLEM },
      { "jh-skolem-rlv", OptionEnum::JH_SKOLEM_RLV },
      { "input-language", OptionEnum::LANG },
      { "lang", OptionEnum::LANG },
      { "learned-rewrite", OptionEnum::LEARNED_REWRITE },
      { "lemmas-on-replay-failure", OptionEnum::LEMMAS_ON_REPLAY_FAILURE },
      { "lfsc-expand-trust", OptionEnum::LFSC_EXPAND_TRUST },
      { "lfsc-flatten", OptionEnum::LFSC_FLATTEN },
      { "literal-matching", OptionEnum::LITERAL_MATCHING },
      { "macros-quant", OptionEnum::MACROS_QUANT },
      { "macros-quant-mode", OptionEnum::MACROS_QUANT_MODE },
      { "maxCutsInContext", OptionEnum::MAXCUTSINCONTEXT },
      { "mbqi", OptionEnum::MBQI },
      { "mbqi-interleave", OptionEnum::MBQI_INTERLEAVE },
      { "mbqi-one-inst-per-round", OptionEnum::MBQI_ONE_INST_PER_ROUND },
      { "minimal-unsat-cores", OptionEnum::MINIMAL_UNSAT_CORES },
      { "minisat-dump-dimacs", OptionEnum::MINISAT_DUMP_DIMACS },
      { "minisat-simplification", OptionEnum::MINISAT_SIMPLIFICATION },
      { "miniscope-quant", OptionEnum::MINISCOPE_QUANT },
      { "miplib-trick", OptionEnum::MIPLIB_TRICK },
      { "miplib-trick-subs", OptionEnum::MIPLIB_TRICK_SUBS },
      { "model-cores", OptionEnum::MODEL_CORES },
      { "model-u-print", OptionEnum::MODEL_U_PRINT },
      { "model-var-elim-uneval", OptionEnum::MODEL_VAR_ELIM_UNEVAL },
      { "multi-trigger-cache", OptionEnum::MULTI_TRIGGER_CACHE },
      { "multi-trigger-linear", OptionEnum::MULTI_TRIGGER_LINEAR },
      { "multi-trigger-priority", OptionEnum::MULTI_TRIGGER_PRIORITY },
      { "multi-trigger-when-single", OptionEnum::MULTI_TRIGGER_WHEN_SINGLE },
      { "new-prop", OptionEnum::NEW_PROP },
      { "nl-cov", OptionEnum::NL_COV },
      { "nl-cov-force", OptionEnum::NL_COV_FORCE },
      { "nl-cov-lift", OptionEnum::NL_COV_LIFT },
      { "nl-cov-linear-model", OptionEnum::NL_COV_LINEAR_MODEL },
      { "nl-cov-proj", OptionEnum::NL_COV_PROJ },
      { "nl-cov-prune", OptionEnum::NL_COV_PRUNE },
      { "nl-cov-var-elim", OptionEnum::NL_COV_VAR_ELIM },
      { "nl-ext", OptionEnum::NL_EXT },
      { "nl-ext-ent-conf", OptionEnum::NL_EXT_ENT_CONF },
      { "nl-ext-factor", OptionEnum::NL_EXT_FACTOR },
      { "nl-ext-inc-prec", OptionEnum::NL_EXT_INC_PREC },
      { "nl-ext-purify", OptionEnum::NL_EXT_PURIFY },
      { "nl-ext-rbound", OptionEnum::NL_EXT_RBOUND },
      { "nl-ext-rewrite", OptionEnum::NL_EXT_REWRITE },
      { "nl-ext-split-zero", OptionEnum::NL_EXT_SPLIT_ZERO },
      { "nl-ext-tf-taylor-deg", OptionEnum::NL_EXT_TF_TAYLOR_DEG },
      { "nl-ext-tf-tplanes", OptionEnum::NL_EXT_TF_TPLANES },
      { "nl-ext-tplanes", OptionEnum::NL_EXT_TPLANES },
      { "nl-ext-tplanes-interleave", OptionEnum::NL_EXT_TPLANES_INTERLEAVE },
      { "nl-icp", OptionEnum::NL_ICP },
      { "nl-rlv", OptionEnum::NL_RLV },
      { "nl-rlv-assert-bounds", OptionEnum::NL_RLV_ASSERT_BOUNDS },
      { "on-repeat-ite-simp", OptionEnum::ON_REPEAT_ITE_SIMP },
      { "opt-res-reconstruction-size", OptionEnum::OPT_RES_RECONSTRUCTION_SIZE },
      { "oracles", OptionEnum::ORACLES },
      { "out", OptionEnum::OUT },
      { "regular-output-channel", OptionEnum::OUT },
      { "output", OptionEnum::OUTPUT },
      { "output-language", OptionEnum::OUTPUT_LANG },
      { "output-lang", OptionEnum::OUTPUT_LANG },
      { "parse-only", OptionEnum::PARSE_ONLY },
      { "partial-triggers", OptionEnum::PARTIAL_TRIGGERS },
      { "check", OptionEnum::PARTITION_CHECK },
      { "partition-check", OptionEnum::PARTITION_CHECK },
      { "partition-conflict-size", OptionEnum::PARTITION_CONFLICT_SIZE },
      { "partition-strategy", OptionEnum::PARTITION_STRATEGY },
      { "partition", OptionEnum::PARTITION_STRATEGY },
      { "pb-rewrites", OptionEnum::PB_REWRITES },
      { "pivot-threshold", OptionEnum::PIVOT_THRESHOLD },
      { "pool-inst", OptionEnum::POOL_INST },
      { "portfolio-jobs", OptionEnum::PORTFOLIO_JOBS },
      { "pp-assert-max-sub-size", OptionEnum::PP_ASSERT_MAX_SUB_SIZE },
      { "pre-skolem-quant", OptionEnum::PRE_SKOLEM_QUANT },
      { "pre-skolem-quant-nested", OptionEnum::PRE_SKOLEM_QUANT_NESTED },
      { "prenex-quant", OptionEnum::PRENEX_QUANT },
      { "prenex-quant-user", OptionEnum::PRENEX_QUANT_USER },
      { "preprocess-only", OptionEnum::PREPROCESS_ONLY },
      { "preregister-mode", OptionEnum::PREREGISTER_MODE },
      { "print-dot-clusters", OptionEnum::PRINT_DOT_CLUSTERS },
      { "print-inst", OptionEnum::PRINT_INST },
      { "print-inst-full", OptionEnum::PRINT_INST_FULL },
      { "print-success", OptionEnum::PRINT_SUCCESS },
      { "print-unsat-cores-full", OptionEnum::PRINT_UNSAT_CORES_FULL },
      { "produce-abducts", OptionEnum::PRODUCE_ABDUCTS },
      { "produce-assertions", OptionEnum::PRODUCE_ASSERTIONS },
      { "interactive-mode", OptionEnum::PRODUCE_ASSERTIONS },
      { "produce-assignments", OptionEnum::PRODUCE_ASSIGNMENTS },
      { "produce-difficulty", OptionEnum::PRODUCE_DIFFICULTY },
      { "produce-interpolants", OptionEnum::PRODUCE_INTERPOLANTS },
      { "produce-learned-literals", OptionEnum::PRODUCE_LEARNED_LITERALS },
      { "produce-models", OptionEnum::PRODUCE_MODELS },
      { "produce-proofs", OptionEnum::PRODUCE_PROOFS },
      { "produce-unsat-assumptions", OptionEnum::PRODUCE_UNSAT_ASSUMPTIONS },
      { "produce-unsat-cores", OptionEnum::PRODUCE_UNSAT_CORES },
      { "proof-alethe-res-pivots", OptionEnum::PROOF_ALETHE_RES_PIVOTS },
      { "proof-annotate", OptionEnum::PROOF_ANNOTATE },
      { "proof-check", OptionEnum::PROOF_CHECK },
      { "proof-dot-dag", OptionEnum::PROOF_DOT_DAG },
      { "proof-format-mode", OptionEnum::PROOF_FORMAT_MODE },
      { "proof-granularity", OptionEnum::PROOF_GRANULARITY },
      { "proof-mode", OptionEnum::PROOF_MODE },
      { "proof-pedantic", OptionEnum::PROOF_PEDANTIC },
      { "proof-pp-merge", OptionEnum::PROOF_PP_MERGE },
      { "proof-print-conclusion", OptionEnum::PROOF_PRINT_CONCLUSION },
      { "proof-prune-input", OptionEnum::PROOF_PRUNE_INPUT },
      { "proof-rewrite-rcons-limit", OptionEnum::PROOF_REWRITE_RCONS_LIMIT },
      { "prop-row-length", OptionEnum::PROP_ROW_LENGTH },
      { "purify-triggers", OptionEnum::PURIFY_TRIGGERS },
      { "quant-alpha-equiv", OptionEnum::QUANT_ALPHA_EQUIV },
      { "quant-dsplit", OptionEnum::QUANT_DSPLIT },
      { "quant-fun-wd", OptionEnum::QUANT_FUN_WD },
      { "quant-ind", OptionEnum::QUANT_IND },
      { "quant-rep-mode", OptionEnum::QUANT_REP_MODE },
      { "quiet", OptionEnum::QUIET },
      { "random-frequency", OptionEnum::RANDOM_FREQ },
      { "random-freq", OptionEnum::RANDOM_FREQ },
      { "re-elim", OptionEnum::RE_ELIM },
      { "re-inter-mode", OptionEnum::RE_INTER_MODE },
      { "register-quant-body-terms", OptionEnum::REGISTER_QUANT_BODY_TERMS },
      { "relational-triggers", OptionEnum::RELATIONAL_TRIGGERS },
      { "relevance-filter", OptionEnum::RELEVANCE_FILTER },
      { "relevant-triggers", OptionEnum::RELEVANT_TRIGGERS },
      { "repeat-simp", OptionEnum::REPEAT_SIMP },
      { "replay-early-close-depth", OptionEnum::REPLAY_EARLY_CLOSE_DEPTH },
      { "replay-lemma-reject-cut", OptionEnum::REPLAY_LEMMA_REJECT_CUT },
      { "replay-num-err-penalty", OptionEnum::REPLAY_NUM_ERR_PENALTY },
      { "replay-reject-cut", OptionEnum::REPLAY_REJECT_CUT },
      { "restart-int-base", OptionEnum::RESTART_INT_BASE },
      { "restart-int-inc", OptionEnum::RESTART_INT_INC },
      { "restrict-pivots", OptionEnum::RESTRICT_PIVOTS },
      { "revert-arith-models-on-unsat", OptionEnum::REVERT_ARITH_MODELS_ON_UNSAT },
      { "rlimit", OptionEnum::RLIMIT },
      { "reproducible-resource-limit", OptionEnum::RLIMIT_PER },
      { "rlimit-per", OptionEnum::RLIMIT_PER },
      { "rr-turns", OptionEnum::RR_TURNS },
      { "rweight", OptionEnum::RWEIGHT },
      { "sat-random-seed", OptionEnum::SAT_RANDOM_SEED },
      { "se-solve-int", OptionEnum::SE_SOLVE_INT },
      { "seed", OptionEnum::SEED },
      { "segv-spin", OptionEnum::SEGV_SPIN },
      { "semantic-checks", OptionEnum::SEMANTIC_CHECKS },
      { "sep-min-refine", OptionEnum::SEP_MIN_REFINE },
      { "sep-pre-skolem-emp", OptionEnum::SEP_PRE_SKOLEM_EMP },
      { "seq-array", OptionEnum::SEQ_ARRAY },
      { "sets-ext", OptionEnum::SETS_EXT },
      { "sets-infer-as-lemmas", OptionEnum::SETS_INFER_AS_LEMMAS },
      { "sets-proxy-lemmas", OptionEnum::SETS_PROXY_LEMMAS },
      { "show-config", OptionEnum::SHOW_CONFIG },
      { "show-trace-tags", OptionEnum::SHOW_TRACE_TAGS },
      { "simp-ite-compress", OptionEnum::SIMP_ITE_COMPRESS },
      { "simp-with-care", OptionEnum::SIMP_WITH_CARE },
      { "simplex-check-period", OptionEnum::SIMPLEX_CHECK_PERIOD },
      { "simplification-mode", OptionEnum::SIMPLIFICATION },
      { "simplification", OptionEnum::SIMPLIFICATION },
      { "simplification-bcp", OptionEnum::SIMPLIFICATION_BCP },
      { "soi-qe", OptionEnum::SOI_QE },
      { "solve-bv-as-int", OptionEnum::SOLVE_BV_AS_INT },
      { "solve-int-as-bv", OptionEnum::SOLVE_INT_AS_BV },
      { "solve-real-as-int", OptionEnum::SOLVE_REAL_AS_INT },
      { "sort-inference", OptionEnum::SORT_INFERENCE },
      { "standard-effort-variable-order-pivots", OptionEnum::STANDARD_EFFORT_VARIABLE_ORDER_PIVOTS },
      { "static-learning", OptionEnum::STATIC_LEARNING },
      { "stats", OptionEnum::STATS },
      { "stats-all", OptionEnum::STATS_ALL },
      { "stats-every-query", OptionEnum::STATS_EVERY_QUERY },
      { "stats-internal", OptionEnum::STATS_INTERNAL },
      { "stdin-input-per-line", OptionEnum::STDIN_INPUT_PER_LINE },
      { "strict-parsing", OptionEnum::STRICT_PARSING },
      { "strings-alpha-card", OptionEnum::STRINGS_ALPHA_CARD },
      { "strings-check-entail-len", OptionEnum::STRINGS_CHECK_ENTAIL_LEN },
      { "strings-code-elim", OptionEnum::STRINGS_CODE_ELIM },
      { "strings-deq-ext", OptionEnum::STRINGS_DEQ_EXT },
      { "strings-eager-eval", OptionEnum::STRINGS_EAGER_EVAL },
      { "strings-eager-len-re", OptionEnum::STRINGS_EAGER_LEN_RE },
      { "strings-eager-reg", OptionEnum::STRINGS_EAGER_REG },
      { "strings-eager-solver", OptionEnum::STRINGS_EAGER_SOLVER },
      { "strings-exp", OptionEnum::STRINGS_EXP },
      { "strings-ff", OptionEnum::STRINGS_FF },
      { "strings-fmf", OptionEnum::STRINGS_FMF },
      { "strings-infer-as-lemmas", OptionEnum::STRINGS_INFER_AS_LEMMAS },
      { "strings-infer-sym", OptionEnum::STRINGS_INFER_SYM },
      { "strings-lazy-pp", OptionEnum::STRINGS_LAZY_PP },
      { "strings-len-norm", OptionEnum::STRINGS_LEN_NORM },
      { "strings-mbr", OptionEnum::STRINGS_MBR },
      { "strings-model-max-len", OptionEnum::STRINGS_MODEL_MAX_LEN },
      { "strings-process-loop-mode", OptionEnum::STRINGS_PROCESS_LOOP_MODE },
      { "strings-re-posc-eager", OptionEnum::STRINGS_RE_POSC_EAGER },
      { "strings-regexp-inclusion", OptionEnum::STRINGS_REGEXP_INCLUSION },
      { "strings-rexplain-lemmas", OptionEnum::STRINGS_REXPLAIN_LEMMAS },
      { "sygus", OptionEnum::SYGUS },
      { "sygus-abort-size", OptionEnum::SYGUS_ABORT_SIZE },
      { "sygus-add-const-grammar", OptionEnum::SYGUS_ADD_CONST_GRAMMAR },
      { "sygus-arg-relevant", OptionEnum::SYGUS_ARG_RELEVANT },
      { "sygus-auto-unfold", OptionEnum::SYGUS_AUTO_UNFOLD },
      { "sygus-bool-ite-return-const", OptionEnum::SYGUS_BOOL_ITE_RETURN_CONST },
      { "sygus-core-connective", OptionEnum::SYGUS_CORE_CONNECTIVE },
      { "sygus-crepair-abort", OptionEnum::SYGUS_CREPAIR_ABORT },
      { "sygus-enum", OptionEnum::SYGUS_ENUM },
      { "sygus-enum-fast-num-consts", OptionEnum::SYGUS_ENUM_FAST_NUM_CONSTS },
      { "sygus-enum-random-p", OptionEnum::SYGUS_ENUM_RANDOM_P },
      { "sygus-eval-unfold", OptionEnum::SYGUS_EVAL_UNFOLD },
      { "sygus-expr-miner-check-timeout", OptionEnum::SYGUS_EXPR_MINER_CHECK_TIMEOUT },
      { "sygus-fair", OptionEnum::SYGUS_FAIR },
      { "sygus-fair-max", OptionEnum::SYGUS_FAIR_MAX },
      { "sygus-filter-sol", OptionEnum::SYGUS_FILTER_SOL },
      { "sygus-filter-sol-rev", OptionEnum::SYGUS_FILTER_SOL_REV },
      { "sygus-grammar-cons", OptionEnum::SYGUS_GRAMMAR_CONS },
      { "sygus-grammar-norm", OptionEnum::SYGUS_GRAMMAR_NORM },
      { "sygus-inference", OptionEnum::SYGUS_INFERENCE },
      { "sygus-inst", OptionEnum::SYGUS_INST },
      { "sygus-inst-mode", OptionEnum::SYGUS_INST_MODE },
      { "sygus-inst-scope", OptionEnum::SYGUS_INST_SCOPE },
      { "sygus-inst-term-sel", OptionEnum::SYGUS_INST_TERM_SEL },
      { "sygus-inv-templ", OptionEnum::SYGUS_INV_TEMPL },
      { "sygus-inv-templ-when-sg", OptionEnum::SYGUS_INV_TEMPL_WHEN_SG },
      { "sygus-min-grammar", OptionEnum::SYGUS_MIN_GRAMMAR },
      { "sygus-out", OptionEnum::SYGUS_OUT },
      { "sygus-pbe", OptionEnum::SYGUS_PBE },
      { "sygus-pbe-multi-fair", OptionEnum::SYGUS_PBE_MULTI_FAIR },
      { "sygus-pbe-multi-fair-diff", OptionEnum::SYGUS_PBE_MULTI_FAIR_DIFF },
      { "sygus-qe-preproc", OptionEnum::SYGUS_QE_PREPROC },
      { "sygus-query-gen", OptionEnum::SYGUS_QUERY_GEN },
      { "sygus-query-gen-dump-files", OptionEnum::SYGUS_QUERY_GEN_DUMP_FILES },
      { "sygus-query-gen-thresh", OptionEnum::SYGUS_QUERY_GEN_THRESH },
      { "sygus-rec-fun", OptionEnum::SYGUS_REC_FUN },
      { "sygus-rec-fun-eval-limit", OptionEnum::SYGUS_REC_FUN_EVAL_LIMIT },
      { "sygus-repair-const", OptionEnum::SYGUS_REPAIR_CONST },
      { "sygus-repair-const-timeout", OptionEnum::SYGUS_REPAIR_CONST_TIMEOUT },
      { "sygus-rewriter", OptionEnum::SYGUS_REWRITER },
      { "sygus-rr-synth", OptionEnum::SYGUS_RR_SYNTH },
      { "sygus-rr-synth-accel", OptionEnum::SYGUS_RR_SYNTH_ACCEL },
      { "sygus-rr-synth-check", OptionEnum::SYGUS_RR_SYNTH_CHECK },
      { "sygus-rr-synth-filter-cong", OptionEnum::SYGUS_RR_SYNTH_FILTER_CONG },
      { "sygus-rr-synth-filter-match", OptionEnum::SYGUS_RR_SYNTH_FILTER_MATCH },
      { "sygus-rr-synth-filter-nl", OptionEnum::SYGUS_RR_SYNTH_FILTER_NL },
      { "sygus-rr-synth-filter-order", OptionEnum::SYGUS_RR_SYNTH_FILTER_ORDER },
      { "sygus-rr-synth-input", OptionEnum::SYGUS_RR_SYNTH_INPUT },
      { "sygus-rr-synth-input-nvars", OptionEnum::SYGUS_RR_SYNTH_INPUT_NVARS },
      { "sygus-rr-synth-input-use-bool", OptionEnum::SYGUS_RR_SYNTH_INPUT_USE_BOOL },
      { "sygus-rr-synth-rec", OptionEnum::SYGUS_RR_SYNTH_REC },
      { "sygus-rr-verify", OptionEnum::SYGUS_RR_VERIFY },
      { "sygus-sample-fp-uniform", OptionEnum::SYGUS_SAMPLE_FP_UNIFORM },
      { "sygus-sample-grammar", OptionEnum::SYGUS_SAMPLE_GRAMMAR },
      { "sygus-samples", OptionEnum::SYGUS_SAMPLES },
      { "sygus-si", OptionEnum::SYGUS_SI },
      { "sygus-si-abort", OptionEnum::SYGUS_SI_ABORT },
      { "sygus-si-rcons", OptionEnum::SYGUS_SI_RCONS },
      { "sygus-si-rcons-limit", OptionEnum::SYGUS_SI_RCONS_LIMIT },
      { "sygus-simple-sym-break", OptionEnum::SYGUS_SIMPLE_SYM_BREAK },
      { "sygus-stream", OptionEnum::SYGUS_STREAM },
      { "sygus-sym-break-lazy", OptionEnum::SYGUS_SYM_BREAK_LAZY },
      { "sygus-sym-break-pbe", OptionEnum::SYGUS_SYM_BREAK_PBE },
      { "sygus-sym-break-rlv", OptionEnum::SYGUS_SYM_BREAK_RLV },
      { "sygus-unif-cond-independent-no-repeat-sol", OptionEnum::SYGUS_UNIF_COND_INDEPENDENT_NO_REPEAT_SOL },
      { "sygus-unif-pi", OptionEnum::SYGUS_UNIF_PI },
      { "sygus-unif-shuffle-cond", OptionEnum::SYGUS_UNIF_SHUFFLE_COND },
      { "sygus-verify-inst-max-rounds", OptionEnum::SYGUS_VERIFY_INST_MAX_ROUNDS },
      { "sygus-verify-timeout", OptionEnum::SYGUS_VERIFY_TIMEOUT },
      { "symmetry-breaker", OptionEnum::SYMMETRY_BREAKER },
      { "tc-mode", OptionEnum::TC_MODE },
      { "term-db-cd", OptionEnum::TERM_DB_CD },
      { "term-db-mode", OptionEnum::TERM_DB_MODE },
      { "theoryof-mode", OptionEnum::THEORYOF_MODE },
      { "tlimit", OptionEnum::TLIMIT },
      { "tlimit-per", OptionEnum::TLIMIT_PER },
      { "trace", OptionEnum::TRACE },
      { "trigger-active-sel", OptionEnum::TRIGGER_ACTIVE_SEL },
      { "trigger-sel", OptionEnum::TRIGGER_SEL },
      { "type-checking", OptionEnum::TYPE_CHECKING },
      { "uf-ho-ext", OptionEnum::UF_HO_EXT },
      { "uf-lazy-ll", OptionEnum::UF_LAZY_LL },
      { "uf-ss", OptionEnum::UF_SS },
      { "uf-ss-abort-card", OptionEnum::UF_SS_ABORT_CARD },
      { "uf-ss-fair", OptionEnum::UF_SS_FAIR },
      { "uf-ss-fair-monotone", OptionEnum::UF_SS_FAIR_MONOTONE },
      { "unate-lemmas", OptionEnum::UNATE_LEMMAS },
      { "unconstrained-simp", OptionEnum::UNCONSTRAINED_SIMP },
      { "unsat-cores-mode", OptionEnum::UNSAT_CORES_MODE },
      { "use-approx", OptionEnum::USE_APPROX },
      { "use-fcsimplex", OptionEnum::USE_FCSIMPLEX },
      { "use-portfolio", OptionEnum::USE_PORTFOLIO },
      { "use-soi", OptionEnum::USE_SOI },
      { "user-pat", OptionEnum::USER_PAT },
      { "user-pool", OptionEnum::USER_POOL },
      { "var-elim-quant", OptionEnum::VAR_ELIM_QUANT },
      { "var-ineq-elim-quant", OptionEnum::VAR_INEQ_ELIM_QUANT },
      { "verbose", OptionEnum::VERBOSE },
      { "verbosity", OptionEnum::VERBOSITY },
      { "version", OptionEnum::VERSION },
      { "wf-checking", OptionEnum::WF_CHECKING },
      { "write-partitions-to", OptionEnum::WRITE_PARTITIONS_TO },
      { "partitions-out", OptionEnum::WRITE_PARTITIONS_TO },
    };
  // clang-format on
}

namespace cvc5::internal::options
{
  // Contains the default option handlers (i.e. parsers)
  namespace handlers {

  /**
   * Utility function for handling numeric options. Takes care of checking for
   * unsignedness, parsing and handling parsing exceptions. Expects `conv` to be
   * a conversion function like `std::stod`, accepting a `std::string` and a
   * `size_t*`. The argument `type` is only used to generate proper error
   * messages and should be the string representation of `T`. If `T` is
   * unsigned, checks that `optionarg` contains no minus. Then `conv` is called
   * and the error conditions are handled: `conv` may throw an exception or
   * `pos` may be smaller than the size of `optionarg`, indicating that not the
   * entirety of `optionarg` was parsed.
   */
  template <typename T, typename FF>
  T parseNumber(const std::string& flag,
                const std::string& optionarg,
                FF&& conv,
                const std::string& type)
  {
    if (!std::numeric_limits<T>::is_signed
        && (optionarg.find('-') != std::string::npos))
    {
      std::stringstream ss;
      ss << "Argument '" << optionarg << "' for " << type << " option " << flag
         << " is negative";
      throw OptionException(ss.str());
    }
    size_t pos = 0;
    T res;
    try
    {
      res = conv(optionarg, &pos);
    }
    catch (const std::exception& e)
    {
      std::stringstream ss;
      ss << "Argument '" << optionarg << "' for " << type << " option " << flag
         << " did not parse as " << type;
      throw OptionException(ss.str());
    }
    if (pos < optionarg.size())
    {
      std::stringstream ss;
      ss << "Argument '" << optionarg << "' for " << type << " option " << flag
         << " did parse only partially as " << type << ", leaving '"
         << optionarg.substr(pos) << "'";
      throw OptionException(ss.str());
    }
    return res;
  }

  /** Default handler that triggers a compiler error */
  template <typename T>
  T handleOption(const std::string& flag, const std::string& optionarg)
  {
    T::unsupported_handleOption_specialization;
    return *static_cast<T*>(nullptr);
  }

  /** Handle a string option by returning it as is. */
  template <>
  std::string handleOption<std::string>(const std::string& flag,
                                        const std::string& optionarg)
  {
    return optionarg;
  }
  /** Handle a bool option, recognizing "true" or "false". */
  template <>
  bool handleOption<bool>(const std::string& flag, const std::string& optionarg)
  {
    if (optionarg == "true")
    {
      return true;
    }
    if (optionarg == "false")
    {
      return false;
    }
    throw OptionException("Argument '" + optionarg + "' for bool option " + flag
                          + " is not a bool constant");
  }

  /** Handle a double option, using `parseNumber` with `std::stod`. */
  template <>
  double handleOption<double>(const std::string& flag,
                              const std::string& optionarg)
  {
    return parseNumber<double>(
        flag,
        optionarg,
        [](const auto& s, auto p) { return std::stod(s, p); },
        "double");
  }

  /** Handle a int64_t option, using `parseNumber` with `std::stoll`. */
  template <>
  int64_t handleOption<int64_t>(const std::string& flag,
                                const std::string& optionarg)
  {
    return parseNumber<int64_t>(
        flag,
        optionarg,
        [](const auto& s, auto p) { return std::stoll(s, p); },
        "int64_t");
  }

  /** Handle a uint64_t option, using `parseNumber` with `std::stoull`. */
  template <>
  uint64_t handleOption<uint64_t>(const std::string& flag,
                                  const std::string& optionarg)
  {
    return parseNumber<uint64_t>(
        flag,
        optionarg,
        [](const auto& s, auto p) { return std::stoull(s, p); },
        "uint64_t");
  }

  /** Handle a ManagedIn option. */
  template <>
  ManagedIn handleOption<ManagedIn>(const std::string& flag,
                                    const std::string& optionarg)
  {
    ManagedIn res;
    res.open(optionarg);
    return res;
  }

  /** Handle a ManagedErr option. */
  template <>
  ManagedErr handleOption<ManagedErr>(const std::string& flag,
                                      const std::string& optionarg)
  {
    ManagedErr res;
    res.open(optionarg);
    return res;
  }

  /** Handle a ManagedOut option. */
  template <>
  ManagedOut handleOption<ManagedOut>(const std::string& flag,
                                      const std::string& optionarg)
  {
    ManagedOut res;
    res.open(optionarg);
    return res;
  }
  }

  std::vector<std::string> getNames()
  {
    return {
        // clang-format off
    "abstract-values", "ackermann", "append-learned-literals-to-cubes",
    "approx-branch-depth", "arith-brab", "arith-eq-solver",
    "arith-no-partial-fun", "arith-prop", "arith-prop-clauses",
    "arith-rewrite-equalities", "arith-static-learning", "arrays-eager-index",
    "arrays-eager-lemmas", "arrays-exp", "arrays-optimize-linear",
    "arrays-prop", "arrays-reduce-sharing", "arrays-weak-equiv",
    "assign-function-values", "bitblast", "bitwise-eq", "bool-to-bv",
    "bv-assert-input", "bv-eager-eval", "bv-gauss-elim", "bv-intro-pow2",
    "bv-print-consts-as-indexed-symbols", "bv-propagate", "bv-rw-extend-eq",
    "bv-sat-solver", "bv-solver", "bv-to-bool", "bv-to-int-use-pow2",
    "bvand-integer-granularity", "cbqi", "cbqi-all-conflict",
    "cbqi-eager-check-rd", "cbqi-eager-test", "cbqi-mode", "cbqi-skip-rd",
    "cbqi-tconstraint", "cbqi-vo-exp", "cdt-bisimilar", "cegis-sample", "cegqi",
    "cegqi-all", "cegqi-bv", "cegqi-bv-concat-inv", "cegqi-bv-ineq",
    "cegqi-bv-interleave-value", "cegqi-bv-linear", "cegqi-bv-rm-extract",
    "cegqi-bv-solve-nl", "cegqi-full", "cegqi-inf-int", "cegqi-inf-real",
    "cegqi-innermost", "cegqi-midpoint", "cegqi-min-bounds", "cegqi-multi-inst",
    "cegqi-nested-qe", "cegqi-nopt", "cegqi-round-up-lia", "check",
    "check-abducts", "check-interpolants", "check-models", "check-proof-steps",
    "check-proofs", "check-synth-sol", "check-unsat-cores",
    "checks-before-partition", "checks-between-partitions",
    "collect-pivot-stats", "compute-partitions", "cond-var-split-quant",
    "condense-function-values", "conjecture-gen", "conjecture-gen-gt-enum",
    "conjecture-gen-max-depth", "conjecture-gen-per-round", "cons-exp-triggers",
    "copyright", "cut-all-bounded", "dag-thresh", "debug-check-models",
    "decision", "decision-mode", "deep-restart", "deep-restart-factor",
    "diagnostic-output-channel", "difficulty-mode", "dio-decomps", "dio-solver",
    "dio-turns", "dt-binary-split", "dt-blast-splits", "dt-cyclic",
    "dt-infer-as-lemmas", "dt-nested-rec", "dt-polite-optimize", "dt-share-sel",
    "dt-stc-ind", "dt-var-exp-quant", "dump-difficulty", "dump-instantiations",
    "dump-instantiations-debug", "dump-models", "dump-proofs",
    "dump-unsat-cores", "e-matching", "eager-arith-bv-conv", "early-exit",
    "early-ite-removal", "ee-mode", "elim-taut-quant", "enum-inst",
    "enum-inst-interleave", "enum-inst-limit", "enum-inst-rd",
    "enum-inst-stratify", "enum-inst-sum", "err", "error-selection-rule",
    "expr-depth", "ext-rew-prep", "ext-rewrite-quant", "fc-penalties",
    "ff-field-polys", "ff-trace-gb", "filename", "filesystem-access",
    "finite-model-find", "flatten-ho-chains", "flex-parser", "fmf-bound",
    "fmf-bound-blast", "fmf-bound-lazy", "fmf-fun", "fmf-fun-rlv", "fmf-mbqi",
    "fmf-type-completion-thresh", "force-logic",
    "force-no-limit-cpu-while-dump", "foreign-theory-rewrite", "fp-exp",
    "fp-lazy-wb", "full-saturate-quant", "global-declarations", "global-negate",
    "help", "heuristic-pivots", "ho-elim", "ho-elim-store-ax", "ho-matching",
    "ho-merge-term-db", "iand-mode", "ieval", "in", "increment-triggers",
    "incremental", "input-language", "inst-max-level", "inst-max-rounds",
    "inst-no-entail", "inst-when", "inst-when-phase", "int-wf-ind",
    "interactive", "interactive-mode", "interpolants-mode",
    "ite-dtt-split-quant", "ite-lift-quant", "ite-simp", "jh-rlv-order",
    "jh-skolem", "jh-skolem-rlv", "lang", "learned-rewrite",
    "lemmas-on-replay-failure", "lfsc-expand-trust", "lfsc-flatten",
    "literal-matching", "macros-quant", "macros-quant-mode", "maxCutsInContext",
    "mbqi", "mbqi-interleave", "mbqi-one-inst-per-round", "minimal-unsat-cores",
    "minisat-dump-dimacs", "minisat-simplification", "miniscope-quant",
    "miplib-trick", "miplib-trick-subs", "model-cores", "model-u-print",
    "model-var-elim-uneval", "multi-trigger-cache", "multi-trigger-linear",
    "multi-trigger-priority", "multi-trigger-when-single", "new-prop", "nl-cov",
    "nl-cov-force", "nl-cov-lift", "nl-cov-linear-model", "nl-cov-proj",
    "nl-cov-prune", "nl-cov-var-elim", "nl-ext", "nl-ext-ent-conf",
    "nl-ext-factor", "nl-ext-inc-prec", "nl-ext-purify", "nl-ext-rbound",
    "nl-ext-rewrite", "nl-ext-split-zero", "nl-ext-tf-taylor-deg",
    "nl-ext-tf-tplanes", "nl-ext-tplanes", "nl-ext-tplanes-interleave",
    "nl-icp", "nl-rlv", "nl-rlv-assert-bounds", "on-repeat-ite-simp",
    "opt-res-reconstruction-size", "oracles", "out", "output", "output-lang",
    "output-language", "parse-only", "partial-triggers", "partition",
    "partition-check", "partition-conflict-size", "partition-strategy",
    "partitions-out", "pb-rewrites", "pivot-threshold", "pool-inst",
    "portfolio-jobs", "pp-assert-max-sub-size", "pre-skolem-quant",
    "pre-skolem-quant-nested", "prenex-quant", "prenex-quant-user",
    "preprocess-only", "preregister-mode", "print-dot-clusters", "print-inst",
    "print-inst-full", "print-success", "print-unsat-cores-full",
    "produce-abducts", "produce-assertions", "produce-assignments",
    "produce-difficulty", "produce-interpolants", "produce-learned-literals",
    "produce-models", "produce-proofs", "produce-unsat-assumptions",
    "produce-unsat-cores", "proof-alethe-res-pivots", "proof-annotate",
    "proof-check", "proof-dot-dag", "proof-format-mode", "proof-granularity",
    "proof-mode", "proof-pedantic", "proof-pp-merge", "proof-print-conclusion",
    "proof-prune-input", "proof-rewrite-rcons-limit", "prop-row-length",
    "purify-triggers", "quant-alpha-equiv", "quant-dsplit", "quant-fun-wd",
    "quant-ind", "quant-rep-mode", "quiet", "random-freq", "random-frequency",
    "re-elim", "re-inter-mode", "register-quant-body-terms",
    "regular-output-channel", "relational-triggers", "relevance-filter",
    "relevant-triggers", "repeat-simp", "replay-early-close-depth",
    "replay-lemma-reject-cut", "replay-num-err-penalty", "replay-reject-cut",
    "reproducible-resource-limit", "restart-int-base", "restart-int-inc",
    "restrict-pivots", "revert-arith-models-on-unsat", "rlimit", "rlimit-per",
    "rr-turns", "rweight", "sat-random-seed", "se-solve-int", "seed",
    "segv-spin", "semantic-checks", "sep-min-refine", "sep-pre-skolem-emp",
    "seq-array", "sets-ext", "sets-infer-as-lemmas", "sets-proxy-lemmas",
    "show-config", "show-trace-tags", "simp-ite-compress", "simp-with-care",
    "simplex-check-period", "simplification", "simplification-bcp",
    "simplification-mode", "soi-qe", "solve-bv-as-int", "solve-int-as-bv",
    "solve-real-as-int", "sort-inference",
    "standard-effort-variable-order-pivots", "static-learning", "stats",
    "stats-all", "stats-every-query", "stats-internal", "stdin-input-per-line",
    "strict-parsing", "strings-alpha-card", "strings-check-entail-len",
    "strings-code-elim", "strings-deq-ext", "strings-eager-eval",
    "strings-eager-len-re", "strings-eager-reg", "strings-eager-solver",
    "strings-exp", "strings-ff", "strings-fmf", "strings-infer-as-lemmas",
    "strings-infer-sym", "strings-lazy-pp", "strings-len-norm", "strings-mbr",
    "strings-model-max-len", "strings-process-loop-mode",
    "strings-re-posc-eager", "strings-regexp-inclusion",
    "strings-rexplain-lemmas", "sygus", "sygus-abort-size",
    "sygus-add-const-grammar", "sygus-arg-relevant", "sygus-auto-unfold",
    "sygus-bool-ite-return-const", "sygus-core-connective",
    "sygus-crepair-abort", "sygus-enum", "sygus-enum-fast-num-consts",
    "sygus-enum-random-p", "sygus-eval-unfold",
    "sygus-expr-miner-check-timeout", "sygus-fair", "sygus-fair-max",
    "sygus-filter-sol", "sygus-filter-sol-rev", "sygus-grammar-cons",
    "sygus-grammar-norm", "sygus-inference", "sygus-inst", "sygus-inst-mode",
    "sygus-inst-scope", "sygus-inst-term-sel", "sygus-inv-templ",
    "sygus-inv-templ-when-sg", "sygus-min-grammar", "sygus-out", "sygus-pbe",
    "sygus-pbe-multi-fair", "sygus-pbe-multi-fair-diff", "sygus-qe-preproc",
    "sygus-query-gen", "sygus-query-gen-dump-files", "sygus-query-gen-thresh",
    "sygus-rec-fun", "sygus-rec-fun-eval-limit", "sygus-repair-const",
    "sygus-repair-const-timeout", "sygus-rewriter", "sygus-rr-synth",
    "sygus-rr-synth-accel", "sygus-rr-synth-check",
    "sygus-rr-synth-filter-cong", "sygus-rr-synth-filter-match",
    "sygus-rr-synth-filter-nl", "sygus-rr-synth-filter-order",
    "sygus-rr-synth-input", "sygus-rr-synth-input-nvars",
    "sygus-rr-synth-input-use-bool", "sygus-rr-synth-rec", "sygus-rr-verify",
    "sygus-sample-fp-uniform", "sygus-sample-grammar", "sygus-samples",
    "sygus-si", "sygus-si-abort", "sygus-si-rcons", "sygus-si-rcons-limit",
    "sygus-simple-sym-break", "sygus-stream", "sygus-sym-break-lazy",
    "sygus-sym-break-pbe", "sygus-sym-break-rlv",
    "sygus-unif-cond-independent-no-repeat-sol", "sygus-unif-pi",
    "sygus-unif-shuffle-cond", "sygus-verify-inst-max-rounds",
    "sygus-verify-timeout", "symmetry-breaker", "tc-mode", "term-db-cd",
    "term-db-mode", "theoryof-mode", "tlimit", "tlimit-per", "trace",
    "trigger-active-sel", "trigger-sel", "type-checking", "uf-ho-ext",
    "uf-lazy-ll", "uf-ss", "uf-ss-abort-card", "uf-ss-fair",
    "uf-ss-fair-monotone", "unate-lemmas", "unconstrained-simp",
    "unsat-cores-mode", "use-approx", "use-fcsimplex", "use-portfolio",
    "use-soi", "user-pat", "user-pool", "var-elim-quant", "var-ineq-elim-quant",
    "verbose", "verbosity", "version", "wf-checking", "write-partitions-to"
        // clang-format on
    };
  }

  std::string get(const Options& options, const std::string& name)
  {
    Trace("options") << "Options::getOption(" << name << ")" << std::endl;
    // clang-format off
    auto it = NAME_TO_ENUM.find(name);
    if (it == NAME_TO_ENUM.end()) {
      throw OptionException("Unrecognized option key or setting: " + name);
    }
    switch (it->second) {
      case OptionEnum::ABSTRACT_VALUES: return options.smt.abstractValues ? "true" : "false";
      case OptionEnum::ACKERMANN: return options.smt.ackermann ? "true" : "false";
      case OptionEnum::APPEND_LEARNED_LITERALS_TO_CUBES: return options.parallel.appendLearnedLiteralsToCubes ? "true" : "false";
      case OptionEnum::APPROX_BRANCH_DEPTH: return std::to_string(options.arith.maxApproxDepth);
      case OptionEnum::ARITH_BRAB: return options.arith.brabTest ? "true" : "false";
      case OptionEnum::ARITH_EQ_SOLVER: return options.arith.arithEqSolver ? "true" : "false";
      case OptionEnum::ARITH_NO_PARTIAL_FUN: return options.arith.arithNoPartialFun ? "true" : "false";
      case OptionEnum::ARITH_PROP: { std::stringstream s; s << options.arith.arithPropagationMode; return s.str(); }
      case OptionEnum::ARITH_PROP_CLAUSES: return std::to_string(options.arith.arithPropAsLemmaLength);
      case OptionEnum::ARITH_REWRITE_EQUALITIES: return options.arith.arithRewriteEq ? "true" : "false";
      case OptionEnum::ARITH_STATIC_LEARNING: return options.arith.arithStaticLearning ? "true" : "false";
      case OptionEnum::ARRAYS_EAGER_INDEX: return options.arrays.arraysEagerIndexSplitting ? "true" : "false";
      case OptionEnum::ARRAYS_EAGER_LEMMAS: return options.arrays.arraysEagerLemmas ? "true" : "false";
      case OptionEnum::ARRAYS_EXP: return options.arrays.arraysExp ? "true" : "false";
      case OptionEnum::ARRAYS_OPTIMIZE_LINEAR: return options.arrays.arraysOptimizeLinear ? "true" : "false";
      case OptionEnum::ARRAYS_PROP: return std::to_string(options.arrays.arraysPropagate);
      case OptionEnum::ARRAYS_REDUCE_SHARING: return options.arrays.arraysReduceSharing ? "true" : "false";
      case OptionEnum::ARRAYS_WEAK_EQUIV: return options.arrays.arraysWeakEquivalence ? "true" : "false";
      case OptionEnum::ASSIGN_FUNCTION_VALUES: return options.theory.assignFunctionValues ? "true" : "false";
      case OptionEnum::BITBLAST: { std::stringstream s; s << options.bv.bitblastMode; return s.str(); }
      case OptionEnum::BITWISE_EQ: return options.bv.bitwiseEq ? "true" : "false";
      case OptionEnum::BOOL_TO_BV: { std::stringstream s; s << options.bv.boolToBitvector; return s.str(); }
      case OptionEnum::BV_ASSERT_INPUT: return options.bv.bvAssertInput ? "true" : "false";
      case OptionEnum::BV_EAGER_EVAL: return options.bv.bvEagerEval ? "true" : "false";
      case OptionEnum::BV_GAUSS_ELIM: return options.bv.bvGaussElim ? "true" : "false";
      case OptionEnum::BV_INTRO_POW2: return options.bv.bvIntroducePow2 ? "true" : "false";
      case OptionEnum::BV_PRINT_CONSTS_AS_INDEXED_SYMBOLS: return options.printer.bvPrintConstsAsIndexedSymbols ? "true" : "false";
      case OptionEnum::BV_PROPAGATE: return options.bv.bitvectorPropagate ? "true" : "false";
      case OptionEnum::BV_RW_EXTEND_EQ: return options.bv.rwExtendEq ? "true" : "false";
      case OptionEnum::BV_SAT_SOLVER: { std::stringstream s; s << options.bv.bvSatSolver; return s.str(); }
      case OptionEnum::BV_SOLVER: { std::stringstream s; s << options.bv.bvSolver; return s.str(); }
      case OptionEnum::BV_TO_BOOL: return options.bv.bitvectorToBool ? "true" : "false";
      case OptionEnum::BV_TO_INT_USE_POW2: return options.smt.bvToIntUsePow2 ? "true" : "false";
      case OptionEnum::BVAND_INTEGER_GRANULARITY: return std::to_string(options.smt.BVAndIntegerGranularity);
      case OptionEnum::CBQI: return options.quantifiers.conflictBasedInst ? "true" : "false";
      case OptionEnum::CBQI_ALL_CONFLICT: return options.quantifiers.cbqiAllConflict ? "true" : "false";
      case OptionEnum::CBQI_EAGER_CHECK_RD: return options.quantifiers.cbqiEagerCheckRd ? "true" : "false";
      case OptionEnum::CBQI_EAGER_TEST: return options.quantifiers.cbqiEagerTest ? "true" : "false";
      case OptionEnum::CBQI_MODE: { std::stringstream s; s << options.quantifiers.cbqiMode; return s.str(); }
      case OptionEnum::CBQI_SKIP_RD: return options.quantifiers.cbqiSkipRd ? "true" : "false";
      case OptionEnum::CBQI_TCONSTRAINT: return options.quantifiers.cbqiTConstraint ? "true" : "false";
      case OptionEnum::CBQI_VO_EXP: return options.quantifiers.cbqiVoExp ? "true" : "false";
      case OptionEnum::CDT_BISIMILAR: return options.datatypes.cdtBisimilar ? "true" : "false";
      case OptionEnum::CEGIS_SAMPLE: { std::stringstream s; s << options.quantifiers.cegisSample; return s.str(); }
      case OptionEnum::CEGQI: return options.quantifiers.cegqi ? "true" : "false";
      case OptionEnum::CEGQI_ALL: return options.quantifiers.cegqiAll ? "true" : "false";
      case OptionEnum::CEGQI_BV: return options.quantifiers.cegqiBv ? "true" : "false";
      case OptionEnum::CEGQI_BV_CONCAT_INV: return options.quantifiers.cegqiBvConcInv ? "true" : "false";
      case OptionEnum::CEGQI_BV_INEQ: { std::stringstream s; s << options.quantifiers.cegqiBvIneqMode; return s.str(); }
      case OptionEnum::CEGQI_BV_INTERLEAVE_VALUE: return options.quantifiers.cegqiBvInterleaveValue ? "true" : "false";
      case OptionEnum::CEGQI_BV_LINEAR: return options.quantifiers.cegqiBvLinearize ? "true" : "false";
      case OptionEnum::CEGQI_BV_RM_EXTRACT: return options.quantifiers.cegqiBvRmExtract ? "true" : "false";
      case OptionEnum::CEGQI_BV_SOLVE_NL: return options.quantifiers.cegqiBvSolveNl ? "true" : "false";
      case OptionEnum::CEGQI_FULL: return options.quantifiers.cegqiFullEffort ? "true" : "false";
      case OptionEnum::CEGQI_INF_INT: return options.quantifiers.cegqiUseInfInt ? "true" : "false";
      case OptionEnum::CEGQI_INF_REAL: return options.quantifiers.cegqiUseInfReal ? "true" : "false";
      case OptionEnum::CEGQI_INNERMOST: return options.quantifiers.cegqiInnermost ? "true" : "false";
      case OptionEnum::CEGQI_MIDPOINT: return options.quantifiers.cegqiMidpoint ? "true" : "false";
      case OptionEnum::CEGQI_MIN_BOUNDS: return options.quantifiers.cegqiMinBounds ? "true" : "false";
      case OptionEnum::CEGQI_MULTI_INST: return options.quantifiers.cegqiMultiInst ? "true" : "false";
      case OptionEnum::CEGQI_NESTED_QE: return options.quantifiers.cegqiNestedQE ? "true" : "false";
      case OptionEnum::CEGQI_NOPT: return options.quantifiers.cegqiNopt ? "true" : "false";
      case OptionEnum::CEGQI_ROUND_UP_LIA: return options.quantifiers.cegqiRoundUpLowerLia ? "true" : "false";
      case OptionEnum::CHECK_ABDUCTS: return options.smt.checkAbducts ? "true" : "false";
      case OptionEnum::CHECK_INTERPOLANTS: return options.smt.checkInterpolants ? "true" : "false";
      case OptionEnum::CHECK_MODELS: return options.smt.checkModels ? "true" : "false";
      case OptionEnum::CHECK_PROOF_STEPS: return options.proof.checkProofSteps ? "true" : "false";
      case OptionEnum::CHECK_PROOFS: return options.smt.checkProofs ? "true" : "false";
      case OptionEnum::CHECK_SYNTH_SOL: return options.smt.checkSynthSol ? "true" : "false";
      case OptionEnum::CHECK_UNSAT_CORES: return options.smt.checkUnsatCores ? "true" : "false";
      case OptionEnum::CHECKS_BEFORE_PARTITION: return std::to_string(options.parallel.checksBeforePartitioning);
      case OptionEnum::CHECKS_BETWEEN_PARTITIONS: return std::to_string(options.parallel.checksBetweenPartitions);
      case OptionEnum::COLLECT_PIVOT_STATS: return options.arith.collectPivots ? "true" : "false";
      case OptionEnum::COMPUTE_PARTITIONS: return std::to_string(options.parallel.computePartitions);
      case OptionEnum::COND_VAR_SPLIT_QUANT: { std::stringstream s; s << options.quantifiers.condVarSplitQuant; return s.str(); }
      case OptionEnum::CONDENSE_FUNCTION_VALUES: return options.theory.condenseFunctionValues ? "true" : "false";
      case OptionEnum::CONJECTURE_GEN: return options.quantifiers.conjectureGen ? "true" : "false";
      case OptionEnum::CONJECTURE_GEN_GT_ENUM: return std::to_string(options.quantifiers.conjectureGenGtEnum);
      case OptionEnum::CONJECTURE_GEN_MAX_DEPTH: return std::to_string(options.quantifiers.conjectureGenMaxDepth);
      case OptionEnum::CONJECTURE_GEN_PER_ROUND: return std::to_string(options.quantifiers.conjectureGenPerRound);
      case OptionEnum::CONS_EXP_TRIGGERS: return options.quantifiers.consExpandTriggers ? "true" : "false";
      case OptionEnum::COPYRIGHT: return options.driver.showCopyright ? "true" : "false";
      case OptionEnum::CUT_ALL_BOUNDED: return options.arith.doCutAllBounded ? "true" : "false";
      case OptionEnum::DAG_THRESH: return std::to_string(options.printer.dagThresh);
      case OptionEnum::DEBUG_CHECK_MODELS: return options.smt.debugCheckModels ? "true" : "false";
      case OptionEnum::DECISION: { std::stringstream s; s << options.decision.decisionMode; return s.str(); }
      case OptionEnum::DEEP_RESTART: { std::stringstream s; s << options.smt.deepRestartMode; return s.str(); }
      case OptionEnum::DEEP_RESTART_FACTOR: return std::to_string(options.smt.deepRestartFactor);
      case OptionEnum::DIFFICULTY_MODE: { std::stringstream s; s << options.smt.difficultyMode; return s.str(); }
      case OptionEnum::DIO_DECOMPS: return options.arith.exportDioDecompositions ? "true" : "false";
      case OptionEnum::DIO_SOLVER: return options.arith.arithDioSolver ? "true" : "false";
      case OptionEnum::DIO_TURNS: return std::to_string(options.arith.dioSolverTurns);
      case OptionEnum::DT_BINARY_SPLIT: return options.datatypes.dtBinarySplit ? "true" : "false";
      case OptionEnum::DT_BLAST_SPLITS: return options.datatypes.dtBlastSplits ? "true" : "false";
      case OptionEnum::DT_CYCLIC: return options.datatypes.dtCyclic ? "true" : "false";
      case OptionEnum::DT_INFER_AS_LEMMAS: return options.datatypes.dtInferAsLemmas ? "true" : "false";
      case OptionEnum::DT_NESTED_REC: return options.datatypes.dtNestedRec ? "true" : "false";
      case OptionEnum::DT_POLITE_OPTIMIZE: return options.datatypes.dtPoliteOptimize ? "true" : "false";
      case OptionEnum::DT_SHARE_SEL: return options.datatypes.dtSharedSelectors ? "true" : "false";
      case OptionEnum::DT_STC_IND: return options.quantifiers.dtStcInduction ? "true" : "false";
      case OptionEnum::DT_VAR_EXP_QUANT: return options.quantifiers.dtVarExpandQuant ? "true" : "false";
      case OptionEnum::DUMP_DIFFICULTY: return options.driver.dumpDifficulty ? "true" : "false";
      case OptionEnum::DUMP_INSTANTIATIONS: return options.driver.dumpInstantiations ? "true" : "false";
      case OptionEnum::DUMP_INSTANTIATIONS_DEBUG: return options.driver.dumpInstantiationsDebug ? "true" : "false";
      case OptionEnum::DUMP_MODELS: return options.driver.dumpModels ? "true" : "false";
      case OptionEnum::DUMP_PROOFS: return options.driver.dumpProofs ? "true" : "false";
      case OptionEnum::DUMP_UNSAT_CORES: return options.driver.dumpUnsatCores ? "true" : "false";
      case OptionEnum::E_MATCHING: return options.quantifiers.eMatching ? "true" : "false";
      case OptionEnum::EAGER_ARITH_BV_CONV: return options.uf.eagerArithBvConv ? "true" : "false";
      case OptionEnum::EARLY_EXIT: return options.driver.earlyExit ? "true" : "false";
      case OptionEnum::EARLY_ITE_REMOVAL: return options.smt.earlyIteRemoval ? "true" : "false";
      case OptionEnum::EE_MODE: { std::stringstream s; s << options.theory.eeMode; return s.str(); }
      case OptionEnum::ELIM_TAUT_QUANT: return options.quantifiers.elimTautQuant ? "true" : "false";
      case OptionEnum::ENUM_INST: return options.quantifiers.enumInst ? "true" : "false";
      case OptionEnum::ENUM_INST_INTERLEAVE: return options.quantifiers.enumInstInterleave ? "true" : "false";
      case OptionEnum::ENUM_INST_LIMIT: return std::to_string(options.quantifiers.enumInstLimit);
      case OptionEnum::ENUM_INST_RD: return options.quantifiers.enumInstRd ? "true" : "false";
      case OptionEnum::ENUM_INST_STRATIFY: return options.quantifiers.enumInstStratify ? "true" : "false";
      case OptionEnum::ENUM_INST_SUM: return options.quantifiers.enumInstSum ? "true" : "false";
      case OptionEnum::ERR: { std::stringstream s; s << options.base.err; return s.str(); }
      case OptionEnum::ERROR_SELECTION_RULE: { std::stringstream s; s << options.arith.arithErrorSelectionRule; return s.str(); }
      case OptionEnum::EXPR_DEPTH: return std::to_string(options.printer.nodeDepth);
      case OptionEnum::EXT_REW_PREP: { std::stringstream s; s << options.smt.extRewPrep; return s.str(); }
      case OptionEnum::EXT_REWRITE_QUANT: return options.quantifiers.extRewriteQuant ? "true" : "false";
      case OptionEnum::FC_PENALTIES: return options.arith.havePenalties ? "true" : "false";
      case OptionEnum::FF_FIELD_POLYS: return options.ff.ffFieldPolys ? "true" : "false";
      case OptionEnum::FF_TRACE_GB: return options.ff.ffTraceGb ? "true" : "false";
      case OptionEnum::FILENAME: return options.driver.filename;
      case OptionEnum::FILESYSTEM_ACCESS: return options.parser.filesystemAccess ? "true" : "false";
      case OptionEnum::FINITE_MODEL_FIND: return options.quantifiers.finiteModelFind ? "true" : "false";
      case OptionEnum::FLATTEN_HO_CHAINS: return options.printer.flattenHOChains ? "true" : "false";
      case OptionEnum::FLEX_PARSER: return options.parser.flexParser ? "true" : "false";
      case OptionEnum::FMF_BOUND: return options.quantifiers.fmfBound ? "true" : "false";
      case OptionEnum::FMF_BOUND_BLAST: return options.quantifiers.fmfBoundBlast ? "true" : "false";
      case OptionEnum::FMF_BOUND_LAZY: return options.quantifiers.fmfBoundLazy ? "true" : "false";
      case OptionEnum::FMF_FUN: return options.quantifiers.fmfFunWellDefined ? "true" : "false";
      case OptionEnum::FMF_FUN_RLV: return options.quantifiers.fmfFunWellDefinedRelevant ? "true" : "false";
      case OptionEnum::FMF_MBQI: { std::stringstream s; s << options.quantifiers.fmfMbqiMode; return s.str(); }
      case OptionEnum::FMF_TYPE_COMPLETION_THRESH: return std::to_string(options.quantifiers.fmfTypeCompletionThresh);
      case OptionEnum::FORCE_LOGIC: return options.parser.forceLogicString;
      case OptionEnum::FORCE_NO_LIMIT_CPU_WHILE_DUMP: return options.driver.forceNoLimitCpuWhileDump ? "true" : "false";
      case OptionEnum::FOREIGN_THEORY_REWRITE: return options.smt.foreignTheoryRewrite ? "true" : "false";
      case OptionEnum::FP_EXP: return options.fp.fpExp ? "true" : "false";
      case OptionEnum::FP_LAZY_WB: return options.fp.fpLazyWb ? "true" : "false";
      case OptionEnum::FULL_SATURATE_QUANT: return options.quantifiers.fullSaturateQuant ? "true" : "false";
      case OptionEnum::GLOBAL_DECLARATIONS: return options.parser.globalDeclarations ? "true" : "false";
      case OptionEnum::GLOBAL_NEGATE: return options.quantifiers.globalNegate ? "true" : "false";
      case OptionEnum::HELP: return options.driver.help ? "true" : "false";
      case OptionEnum::HEURISTIC_PIVOTS: return std::to_string(options.arith.arithHeuristicPivots);
      case OptionEnum::HO_ELIM: return options.quantifiers.hoElim ? "true" : "false";
      case OptionEnum::HO_ELIM_STORE_AX: return options.quantifiers.hoElimStoreAx ? "true" : "false";
      case OptionEnum::HO_MATCHING: return options.quantifiers.hoMatching ? "true" : "false";
      case OptionEnum::HO_MERGE_TERM_DB: return options.quantifiers.hoMergeTermDb ? "true" : "false";
      case OptionEnum::IAND_MODE: { std::stringstream s; s << options.smt.iandMode; return s.str(); }
      case OptionEnum::IEVAL: { std::stringstream s; s << options.quantifiers.ievalMode; return s.str(); }
      case OptionEnum::IN: { std::stringstream s; s << options.base.in; return s.str(); }
      case OptionEnum::INCREMENT_TRIGGERS: return options.quantifiers.incrementTriggers ? "true" : "false";
      case OptionEnum::INCREMENTAL: return options.base.incrementalSolving ? "true" : "false";
      case OptionEnum::INST_MAX_LEVEL: return std::to_string(options.quantifiers.instMaxLevel);
      case OptionEnum::INST_MAX_ROUNDS: return std::to_string(options.quantifiers.instMaxRounds);
      case OptionEnum::INST_NO_ENTAIL: return options.quantifiers.instNoEntail ? "true" : "false";
      case OptionEnum::INST_WHEN: { std::stringstream s; s << options.quantifiers.instWhenMode; return s.str(); }
      case OptionEnum::INST_WHEN_PHASE: return std::to_string(options.quantifiers.instWhenPhase);
      case OptionEnum::INT_WF_IND: return options.quantifiers.intWfInduction ? "true" : "false";
      case OptionEnum::INTERACTIVE: return options.driver.interactive ? "true" : "false";
      case OptionEnum::INTERPOLANTS_MODE: { std::stringstream s; s << options.smt.interpolantsMode; return s.str(); }
      case OptionEnum::ITE_DTT_SPLIT_QUANT: return options.quantifiers.iteDtTesterSplitQuant ? "true" : "false";
      case OptionEnum::ITE_LIFT_QUANT: { std::stringstream s; s << options.quantifiers.iteLiftQuant; return s.str(); }
      case OptionEnum::ITE_SIMP: return options.smt.doITESimp ? "true" : "false";
      case OptionEnum::JH_RLV_ORDER: return options.decision.jhRlvOrder ? "true" : "false";
      case OptionEnum::JH_SKOLEM: { std::stringstream s; s << options.decision.jhSkolemMode; return s.str(); }
      case OptionEnum::JH_SKOLEM_RLV: { std::stringstream s; s << options.decision.jhSkolemRlvMode; return s.str(); }
      case OptionEnum::LANG: { std::stringstream s; s << options.base.inputLanguage; return s.str(); }
      case OptionEnum::LEARNED_REWRITE: return options.smt.learnedRewrite ? "true" : "false";
      case OptionEnum::LEMMAS_ON_REPLAY_FAILURE: return options.arith.replayFailureLemma ? "true" : "false";
      case OptionEnum::LFSC_EXPAND_TRUST: return options.proof.lfscExpandTrust ? "true" : "false";
      case OptionEnum::LFSC_FLATTEN: return options.proof.lfscFlatten ? "true" : "false";
      case OptionEnum::LITERAL_MATCHING: { std::stringstream s; s << options.quantifiers.literalMatchMode; return s.str(); }
      case OptionEnum::MACROS_QUANT: return options.quantifiers.macrosQuant ? "true" : "false";
      case OptionEnum::MACROS_QUANT_MODE: { std::stringstream s; s << options.quantifiers.macrosQuantMode; return s.str(); }
      case OptionEnum::MAXCUTSINCONTEXT: return std::to_string(options.arith.maxCutsInContext);
      case OptionEnum::MBQI: return options.quantifiers.mbqi ? "true" : "false";
      case OptionEnum::MBQI_INTERLEAVE: return options.quantifiers.mbqiInterleave ? "true" : "false";
      case OptionEnum::MBQI_ONE_INST_PER_ROUND: return options.quantifiers.fmfOneInstPerRound ? "true" : "false";
      case OptionEnum::MINIMAL_UNSAT_CORES: return options.smt.minimalUnsatCores ? "true" : "false";
      case OptionEnum::MINISAT_DUMP_DIMACS: return options.prop.minisatDumpDimacs ? "true" : "false";
      case OptionEnum::MINISAT_SIMPLIFICATION: { std::stringstream s; s << options.prop.minisatSimpMode; return s.str(); }
      case OptionEnum::MINISCOPE_QUANT: { std::stringstream s; s << options.quantifiers.miniscopeQuant; return s.str(); }
      case OptionEnum::MIPLIB_TRICK: return options.arith.arithMLTrick ? "true" : "false";
      case OptionEnum::MIPLIB_TRICK_SUBS: return std::to_string(options.arith.arithMLTrickSubstitutions);
      case OptionEnum::MODEL_CORES: { std::stringstream s; s << options.smt.modelCoresMode; return s.str(); }
      case OptionEnum::MODEL_U_PRINT: { std::stringstream s; s << options.printer.modelUninterpPrint; return s.str(); }
      case OptionEnum::MODEL_VAR_ELIM_UNEVAL: return options.smt.modelVarElimUneval ? "true" : "false";
      case OptionEnum::MULTI_TRIGGER_CACHE: return options.quantifiers.multiTriggerCache ? "true" : "false";
      case OptionEnum::MULTI_TRIGGER_LINEAR: return options.quantifiers.multiTriggerLinear ? "true" : "false";
      case OptionEnum::MULTI_TRIGGER_PRIORITY: return options.quantifiers.multiTriggerPriority ? "true" : "false";
      case OptionEnum::MULTI_TRIGGER_WHEN_SINGLE: return options.quantifiers.multiTriggerWhenSingle ? "true" : "false";
      case OptionEnum::NEW_PROP: return options.arith.newProp ? "true" : "false";
      case OptionEnum::NL_COV: return options.arith.nlCov ? "true" : "false";
      case OptionEnum::NL_COV_FORCE: return options.arith.nlCovForce ? "true" : "false";
      case OptionEnum::NL_COV_LIFT: { std::stringstream s; s << options.arith.nlCovLifting; return s.str(); }
      case OptionEnum::NL_COV_LINEAR_MODEL: { std::stringstream s; s << options.arith.nlCovLinearModel; return s.str(); }
      case OptionEnum::NL_COV_PROJ: { std::stringstream s; s << options.arith.nlCovProjection; return s.str(); }
      case OptionEnum::NL_COV_PRUNE: return options.arith.nlCovPrune ? "true" : "false";
      case OptionEnum::NL_COV_VAR_ELIM: return options.arith.nlCovVarElim ? "true" : "false";
      case OptionEnum::NL_EXT: { std::stringstream s; s << options.arith.nlExt; return s.str(); }
      case OptionEnum::NL_EXT_ENT_CONF: return options.arith.nlExtEntailConflicts ? "true" : "false";
      case OptionEnum::NL_EXT_FACTOR: return options.arith.nlExtFactor ? "true" : "false";
      case OptionEnum::NL_EXT_INC_PREC: return options.arith.nlExtIncPrecision ? "true" : "false";
      case OptionEnum::NL_EXT_PURIFY: return options.arith.nlExtPurify ? "true" : "false";
      case OptionEnum::NL_EXT_RBOUND: return options.arith.nlExtResBound ? "true" : "false";
      case OptionEnum::NL_EXT_REWRITE: return options.arith.nlExtRewrites ? "true" : "false";
      case OptionEnum::NL_EXT_SPLIT_ZERO: return options.arith.nlExtSplitZero ? "true" : "false";
      case OptionEnum::NL_EXT_TF_TAYLOR_DEG: return std::to_string(options.arith.nlExtTfTaylorDegree);
      case OptionEnum::NL_EXT_TF_TPLANES: return options.arith.nlExtTfTangentPlanes ? "true" : "false";
      case OptionEnum::NL_EXT_TPLANES: return options.arith.nlExtTangentPlanes ? "true" : "false";
      case OptionEnum::NL_EXT_TPLANES_INTERLEAVE: return options.arith.nlExtTangentPlanesInterleave ? "true" : "false";
      case OptionEnum::NL_ICP: return options.arith.nlICP ? "true" : "false";
      case OptionEnum::NL_RLV: { std::stringstream s; s << options.arith.nlRlvMode; return s.str(); }
      case OptionEnum::NL_RLV_ASSERT_BOUNDS: return options.arith.nlRlvAssertBounds ? "true" : "false";
      case OptionEnum::ON_REPEAT_ITE_SIMP: return options.smt.doITESimpOnRepeat ? "true" : "false";
      case OptionEnum::OPT_RES_RECONSTRUCTION_SIZE: return options.proof.optResReconSize ? "true" : "false";
      case OptionEnum::ORACLES: return options.quantifiers.oracles ? "true" : "false";
      case OptionEnum::OUT: { std::stringstream s; s << options.base.out; return s.str(); }
      case OptionEnum::OUTPUT_LANG: { std::stringstream s; s << options.printer.outputLanguage; return s.str(); }
      case OptionEnum::PARSE_ONLY: return options.base.parseOnly ? "true" : "false";
      case OptionEnum::PARTIAL_TRIGGERS: return options.quantifiers.partialTriggers ? "true" : "false";
      case OptionEnum::PARTITION_CHECK: { std::stringstream s; s << options.parallel.partitionCheck; return s.str(); }
      case OptionEnum::PARTITION_CONFLICT_SIZE: return std::to_string(options.parallel.partitionConflictSize);
      case OptionEnum::PARTITION_STRATEGY: { std::stringstream s; s << options.parallel.partitionStrategy; return s.str(); }
      case OptionEnum::PB_REWRITES: return options.arith.pbRewrites ? "true" : "false";
      case OptionEnum::PIVOT_THRESHOLD: return std::to_string(options.arith.arithPivotThreshold);
      case OptionEnum::POOL_INST: return options.quantifiers.poolInst ? "true" : "false";
      case OptionEnum::PORTFOLIO_JOBS: return std::to_string(options.driver.portfolioJobs);
      case OptionEnum::PP_ASSERT_MAX_SUB_SIZE: return std::to_string(options.arith.ppAssertMaxSubSize);
      case OptionEnum::PRE_SKOLEM_QUANT: { std::stringstream s; s << options.quantifiers.preSkolemQuant; return s.str(); }
      case OptionEnum::PRE_SKOLEM_QUANT_NESTED: return options.quantifiers.preSkolemQuantNested ? "true" : "false";
      case OptionEnum::PRENEX_QUANT: { std::stringstream s; s << options.quantifiers.prenexQuant; return s.str(); }
      case OptionEnum::PRENEX_QUANT_USER: return options.quantifiers.prenexQuantUser ? "true" : "false";
      case OptionEnum::PREPROCESS_ONLY: return options.base.preprocessOnly ? "true" : "false";
      case OptionEnum::PREREGISTER_MODE: { std::stringstream s; s << options.prop.preRegisterMode; return s.str(); }
      case OptionEnum::PRINT_DOT_CLUSTERS: return options.proof.printDotClusters ? "true" : "false";
      case OptionEnum::PRINT_INST: { std::stringstream s; s << options.quantifiers.printInstMode; return s.str(); }
      case OptionEnum::PRINT_INST_FULL: return options.quantifiers.printInstFull ? "true" : "false";
      case OptionEnum::PRINT_SUCCESS: return options.driver.printSuccess ? "true" : "false";
      case OptionEnum::PRINT_UNSAT_CORES_FULL: return options.smt.printUnsatCoresFull ? "true" : "false";
      case OptionEnum::PRODUCE_ABDUCTS: return options.smt.produceAbducts ? "true" : "false";
      case OptionEnum::PRODUCE_ASSERTIONS: return options.smt.produceAssertions ? "true" : "false";
      case OptionEnum::PRODUCE_ASSIGNMENTS: return options.smt.produceAssignments ? "true" : "false";
      case OptionEnum::PRODUCE_DIFFICULTY: return options.smt.produceDifficulty ? "true" : "false";
      case OptionEnum::PRODUCE_INTERPOLANTS: return options.smt.produceInterpolants ? "true" : "false";
      case OptionEnum::PRODUCE_LEARNED_LITERALS: return options.smt.produceLearnedLiterals ? "true" : "false";
      case OptionEnum::PRODUCE_MODELS: return options.smt.produceModels ? "true" : "false";
      case OptionEnum::PRODUCE_PROOFS: return options.smt.produceProofs ? "true" : "false";
      case OptionEnum::PRODUCE_UNSAT_ASSUMPTIONS: return options.smt.unsatAssumptions ? "true" : "false";
      case OptionEnum::PRODUCE_UNSAT_CORES: return options.smt.produceUnsatCores ? "true" : "false";
      case OptionEnum::PROOF_ALETHE_RES_PIVOTS: return options.proof.proofAletheResPivots ? "true" : "false";
      case OptionEnum::PROOF_ANNOTATE: return options.proof.proofAnnotate ? "true" : "false";
      case OptionEnum::PROOF_CHECK: { std::stringstream s; s << options.proof.proofCheck; return s.str(); }
      case OptionEnum::PROOF_DOT_DAG: return options.proof.printDotAsDAG ? "true" : "false";
      case OptionEnum::PROOF_FORMAT_MODE: { std::stringstream s; s << options.proof.proofFormatMode; return s.str(); }
      case OptionEnum::PROOF_GRANULARITY: { std::stringstream s; s << options.proof.proofGranularityMode; return s.str(); }
      case OptionEnum::PROOF_MODE: { std::stringstream s; s << options.smt.proofMode; return s.str(); }
      case OptionEnum::PROOF_PEDANTIC: return std::to_string(options.proof.proofPedantic);
      case OptionEnum::PROOF_PP_MERGE: return options.proof.proofPpMerge ? "true" : "false";
      case OptionEnum::PROOF_PRINT_CONCLUSION: return options.proof.proofPrintConclusion ? "true" : "false";
      case OptionEnum::PROOF_PRUNE_INPUT: return options.proof.proofPruneInput ? "true" : "false";
      case OptionEnum::PROOF_REWRITE_RCONS_LIMIT: return std::to_string(options.proof.proofRewriteRconsRecLimit);
      case OptionEnum::PROP_ROW_LENGTH: return std::to_string(options.arith.arithPropagateMaxLength);
      case OptionEnum::PURIFY_TRIGGERS: return options.quantifiers.purifyTriggers ? "true" : "false";
      case OptionEnum::QUANT_ALPHA_EQUIV: return options.quantifiers.quantAlphaEquiv ? "true" : "false";
      case OptionEnum::QUANT_DSPLIT: { std::stringstream s; s << options.quantifiers.quantDynamicSplit; return s.str(); }
      case OptionEnum::QUANT_FUN_WD: return options.quantifiers.quantFunWellDefined ? "true" : "false";
      case OptionEnum::QUANT_IND: return options.quantifiers.quantInduction ? "true" : "false";
      case OptionEnum::QUANT_REP_MODE: { std::stringstream s; s << options.quantifiers.quantRepMode; return s.str(); }
      case OptionEnum::RANDOM_FREQ: return std::to_string(options.prop.satRandomFreq);
      case OptionEnum::RE_ELIM: { std::stringstream s; s << options.strings.regExpElim; return s.str(); }
      case OptionEnum::RE_INTER_MODE: { std::stringstream s; s << options.strings.stringRegExpInterMode; return s.str(); }
      case OptionEnum::REGISTER_QUANT_BODY_TERMS: return options.quantifiers.registerQuantBodyTerms ? "true" : "false";
      case OptionEnum::RELATIONAL_TRIGGERS: return options.quantifiers.relationalTriggers ? "true" : "false";
      case OptionEnum::RELEVANCE_FILTER: return options.theory.relevanceFilter ? "true" : "false";
      case OptionEnum::RELEVANT_TRIGGERS: return options.quantifiers.relevantTriggers ? "true" : "false";
      case OptionEnum::REPEAT_SIMP: return options.smt.repeatSimp ? "true" : "false";
      case OptionEnum::REPLAY_EARLY_CLOSE_DEPTH: return std::to_string(options.arith.replayEarlyCloseDepths);
      case OptionEnum::REPLAY_LEMMA_REJECT_CUT: return std::to_string(options.arith.lemmaRejectCutSize);
      case OptionEnum::REPLAY_NUM_ERR_PENALTY: return std::to_string(options.arith.replayNumericFailurePenalty);
      case OptionEnum::REPLAY_REJECT_CUT: return std::to_string(options.arith.replayRejectCutSize);
      case OptionEnum::RESTART_INT_BASE: return std::to_string(options.prop.satRestartFirst);
      case OptionEnum::RESTART_INT_INC: return std::to_string(options.prop.satRestartInc);
      case OptionEnum::RESTRICT_PIVOTS: return options.arith.restrictedPivots ? "true" : "false";
      case OptionEnum::REVERT_ARITH_MODELS_ON_UNSAT: return options.arith.revertArithModels ? "true" : "false";
      case OptionEnum::RLIMIT: return std::to_string(options.base.cumulativeResourceLimit);
      case OptionEnum::RLIMIT_PER: return std::to_string(options.base.perCallResourceLimit);
      case OptionEnum::RR_TURNS: return std::to_string(options.arith.rrTurns);
      case OptionEnum::SAT_RANDOM_SEED: return std::to_string(options.prop.satRandomSeed);
      case OptionEnum::SE_SOLVE_INT: return options.arith.trySolveIntStandardEffort ? "true" : "false";
      case OptionEnum::SEED: return std::to_string(options.driver.seed);
      case OptionEnum::SEGV_SPIN: return options.driver.segvSpin ? "true" : "false";
      case OptionEnum::SEMANTIC_CHECKS: return options.parser.semanticChecks ? "true" : "false";
      case OptionEnum::SEP_MIN_REFINE: return options.sep.sepMinimalRefine ? "true" : "false";
      case OptionEnum::SEP_PRE_SKOLEM_EMP: return options.sep.sepPreSkolemEmp ? "true" : "false";
      case OptionEnum::SEQ_ARRAY: { std::stringstream s; s << options.strings.seqArray; return s.str(); }
      case OptionEnum::SETS_EXT: return options.sets.setsExt ? "true" : "false";
      case OptionEnum::SETS_INFER_AS_LEMMAS: return options.sets.setsInferAsLemmas ? "true" : "false";
      case OptionEnum::SETS_PROXY_LEMMAS: return options.sets.setsProxyLemmas ? "true" : "false";
      case OptionEnum::SHOW_CONFIG: return options.driver.showConfiguration ? "true" : "false";
      case OptionEnum::SHOW_TRACE_TAGS: return options.driver.showTraceTags ? "true" : "false";
      case OptionEnum::SIMP_ITE_COMPRESS: return options.smt.compressItes ? "true" : "false";
      case OptionEnum::SIMP_WITH_CARE: return options.smt.simplifyWithCareEnabled ? "true" : "false";
      case OptionEnum::SIMPLEX_CHECK_PERIOD: return std::to_string(options.arith.arithSimplexCheckPeriod);
      case OptionEnum::SIMPLIFICATION: { std::stringstream s; s << options.smt.simplificationMode; return s.str(); }
      case OptionEnum::SIMPLIFICATION_BCP: return options.smt.simplificationBoolConstProp ? "true" : "false";
      case OptionEnum::SOI_QE: return options.arith.soiQuickExplain ? "true" : "false";
      case OptionEnum::SOLVE_BV_AS_INT: { std::stringstream s; s << options.smt.solveBVAsInt; return s.str(); }
      case OptionEnum::SOLVE_INT_AS_BV: return std::to_string(options.smt.solveIntAsBV);
      case OptionEnum::SOLVE_REAL_AS_INT: return options.smt.solveRealAsInt ? "true" : "false";
      case OptionEnum::SORT_INFERENCE: return options.smt.sortInference ? "true" : "false";
      case OptionEnum::STANDARD_EFFORT_VARIABLE_ORDER_PIVOTS: return std::to_string(options.arith.arithStandardCheckVarOrderPivots);
      case OptionEnum::STATIC_LEARNING: return options.smt.staticLearning ? "true" : "false";
      case OptionEnum::STATS: return options.base.statistics ? "true" : "false";
      case OptionEnum::STATS_ALL: return options.base.statisticsAll ? "true" : "false";
      case OptionEnum::STATS_EVERY_QUERY: return options.base.statisticsEveryQuery ? "true" : "false";
      case OptionEnum::STATS_INTERNAL: return options.base.statisticsInternal ? "true" : "false";
      case OptionEnum::STDIN_INPUT_PER_LINE: return options.driver.stdinInputPerLine ? "true" : "false";
      case OptionEnum::STRICT_PARSING: return options.parser.strictParsing ? "true" : "false";
      case OptionEnum::STRINGS_ALPHA_CARD: return std::to_string(options.strings.stringsAlphaCard);
      case OptionEnum::STRINGS_CHECK_ENTAIL_LEN: return options.strings.stringCheckEntailLen ? "true" : "false";
      case OptionEnum::STRINGS_CODE_ELIM: return options.strings.stringsCodeElim ? "true" : "false";
      case OptionEnum::STRINGS_DEQ_EXT: return options.strings.stringsDeqExt ? "true" : "false";
      case OptionEnum::STRINGS_EAGER_EVAL: return options.strings.stringEagerEval ? "true" : "false";
      case OptionEnum::STRINGS_EAGER_LEN_RE: return options.strings.stringsEagerLenEntRegexp ? "true" : "false";
      case OptionEnum::STRINGS_EAGER_REG: return options.strings.stringEagerReg ? "true" : "false";
      case OptionEnum::STRINGS_EAGER_SOLVER: return options.strings.stringEagerSolver ? "true" : "false";
      case OptionEnum::STRINGS_EXP: return options.strings.stringExp ? "true" : "false";
      case OptionEnum::STRINGS_FF: return options.strings.stringFlatForms ? "true" : "false";
      case OptionEnum::STRINGS_FMF: return options.strings.stringFMF ? "true" : "false";
      case OptionEnum::STRINGS_INFER_AS_LEMMAS: return options.strings.stringInferAsLemmas ? "true" : "false";
      case OptionEnum::STRINGS_INFER_SYM: return options.strings.stringInferSym ? "true" : "false";
      case OptionEnum::STRINGS_LAZY_PP: return options.strings.stringLazyPreproc ? "true" : "false";
      case OptionEnum::STRINGS_LEN_NORM: return options.strings.stringLenNorm ? "true" : "false";
      case OptionEnum::STRINGS_MBR: return options.strings.stringModelBasedReduction ? "true" : "false";
      case OptionEnum::STRINGS_MODEL_MAX_LEN: return std::to_string(options.strings.stringsModelMaxLength);
      case OptionEnum::STRINGS_PROCESS_LOOP_MODE: { std::stringstream s; s << options.strings.stringProcessLoopMode; return s.str(); }
      case OptionEnum::STRINGS_RE_POSC_EAGER: return options.strings.stringRegexpPosConcatEager ? "true" : "false";
      case OptionEnum::STRINGS_REGEXP_INCLUSION: return options.strings.stringRegexpInclusion ? "true" : "false";
      case OptionEnum::STRINGS_REXPLAIN_LEMMAS: return options.strings.stringRExplainLemmas ? "true" : "false";
      case OptionEnum::SYGUS: return options.quantifiers.sygus ? "true" : "false";
      case OptionEnum::SYGUS_ABORT_SIZE: return std::to_string(options.datatypes.sygusAbortSize);
      case OptionEnum::SYGUS_ADD_CONST_GRAMMAR: return options.quantifiers.sygusAddConstGrammar ? "true" : "false";
      case OptionEnum::SYGUS_ARG_RELEVANT: return options.quantifiers.sygusArgRelevant ? "true" : "false";
      case OptionEnum::SYGUS_AUTO_UNFOLD: return options.quantifiers.sygusInvAutoUnfold ? "true" : "false";
      case OptionEnum::SYGUS_BOOL_ITE_RETURN_CONST: return options.quantifiers.sygusBoolIteReturnConst ? "true" : "false";
      case OptionEnum::SYGUS_CORE_CONNECTIVE: return options.quantifiers.sygusCoreConnective ? "true" : "false";
      case OptionEnum::SYGUS_CREPAIR_ABORT: return options.quantifiers.sygusConstRepairAbort ? "true" : "false";
      case OptionEnum::SYGUS_ENUM: { std::stringstream s; s << options.quantifiers.sygusEnumMode; return s.str(); }
      case OptionEnum::SYGUS_ENUM_FAST_NUM_CONSTS: return std::to_string(options.quantifiers.sygusEnumFastNumConsts);
      case OptionEnum::SYGUS_ENUM_RANDOM_P: return std::to_string(options.quantifiers.sygusEnumRandomP);
      case OptionEnum::SYGUS_EVAL_UNFOLD: { std::stringstream s; s << options.quantifiers.sygusEvalUnfoldMode; return s.str(); }
      case OptionEnum::SYGUS_EXPR_MINER_CHECK_TIMEOUT: return std::to_string(options.quantifiers.sygusExprMinerCheckTimeout);
      case OptionEnum::SYGUS_FAIR: { std::stringstream s; s << options.datatypes.sygusFair; return s.str(); }
      case OptionEnum::SYGUS_FAIR_MAX: return options.datatypes.sygusFairMax ? "true" : "false";
      case OptionEnum::SYGUS_FILTER_SOL: { std::stringstream s; s << options.quantifiers.sygusFilterSolMode; return s.str(); }
      case OptionEnum::SYGUS_FILTER_SOL_REV: return options.quantifiers.sygusFilterSolRevSubsume ? "true" : "false";
      case OptionEnum::SYGUS_GRAMMAR_CONS: { std::stringstream s; s << options.quantifiers.sygusGrammarConsMode; return s.str(); }
      case OptionEnum::SYGUS_GRAMMAR_NORM: return options.quantifiers.sygusGrammarNorm ? "true" : "false";
      case OptionEnum::SYGUS_INFERENCE: return options.quantifiers.sygusInference ? "true" : "false";
      case OptionEnum::SYGUS_INST: return options.quantifiers.sygusInst ? "true" : "false";
      case OptionEnum::SYGUS_INST_MODE: { std::stringstream s; s << options.quantifiers.sygusInstMode; return s.str(); }
      case OptionEnum::SYGUS_INST_SCOPE: { std::stringstream s; s << options.quantifiers.sygusInstScope; return s.str(); }
      case OptionEnum::SYGUS_INST_TERM_SEL: { std::stringstream s; s << options.quantifiers.sygusInstTermSel; return s.str(); }
      case OptionEnum::SYGUS_INV_TEMPL: { std::stringstream s; s << options.quantifiers.sygusInvTemplMode; return s.str(); }
      case OptionEnum::SYGUS_INV_TEMPL_WHEN_SG: return options.quantifiers.sygusInvTemplWhenSyntax ? "true" : "false";
      case OptionEnum::SYGUS_MIN_GRAMMAR: return options.quantifiers.sygusMinGrammar ? "true" : "false";
      case OptionEnum::SYGUS_OUT: { std::stringstream s; s << options.quantifiers.sygusOut; return s.str(); }
      case OptionEnum::SYGUS_PBE: return options.quantifiers.sygusUnifPbe ? "true" : "false";
      case OptionEnum::SYGUS_PBE_MULTI_FAIR: return options.quantifiers.sygusPbeMultiFair ? "true" : "false";
      case OptionEnum::SYGUS_PBE_MULTI_FAIR_DIFF: return std::to_string(options.quantifiers.sygusPbeMultiFairDiff);
      case OptionEnum::SYGUS_QE_PREPROC: return options.quantifiers.sygusQePreproc ? "true" : "false";
      case OptionEnum::SYGUS_QUERY_GEN: { std::stringstream s; s << options.quantifiers.sygusQueryGen; return s.str(); }
      case OptionEnum::SYGUS_QUERY_GEN_DUMP_FILES: { std::stringstream s; s << options.quantifiers.sygusQueryGenDumpFiles; return s.str(); }
      case OptionEnum::SYGUS_QUERY_GEN_THRESH: return std::to_string(options.quantifiers.sygusQueryGenThresh);
      case OptionEnum::SYGUS_REC_FUN: return options.quantifiers.sygusRecFun ? "true" : "false";
      case OptionEnum::SYGUS_REC_FUN_EVAL_LIMIT: return std::to_string(options.quantifiers.sygusRecFunEvalLimit);
      case OptionEnum::SYGUS_REPAIR_CONST: return options.quantifiers.sygusRepairConst ? "true" : "false";
      case OptionEnum::SYGUS_REPAIR_CONST_TIMEOUT: return std::to_string(options.quantifiers.sygusRepairConstTimeout);
      case OptionEnum::SYGUS_REWRITER: { std::stringstream s; s << options.datatypes.sygusRewriter; return s.str(); }
      case OptionEnum::SYGUS_RR_SYNTH: return options.quantifiers.sygusRewSynth ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_ACCEL: return options.quantifiers.sygusRewSynthAccel ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_CHECK: return options.quantifiers.sygusRewSynthCheck ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_CONG: return options.quantifiers.sygusRewSynthFilterCong ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_MATCH: return options.quantifiers.sygusRewSynthFilterMatch ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_NL: return options.quantifiers.sygusRewSynthFilterNonLinear ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_ORDER: return options.quantifiers.sygusRewSynthFilterOrder ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_INPUT: return options.quantifiers.sygusRewSynthInput ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_INPUT_NVARS: return std::to_string(options.quantifiers.sygusRewSynthInputNVars);
      case OptionEnum::SYGUS_RR_SYNTH_INPUT_USE_BOOL: return options.quantifiers.sygusRewSynthInputUseBool ? "true" : "false";
      case OptionEnum::SYGUS_RR_SYNTH_REC: return options.quantifiers.sygusRewSynthRec ? "true" : "false";
      case OptionEnum::SYGUS_RR_VERIFY: return options.quantifiers.sygusRewVerify ? "true" : "false";
      case OptionEnum::SYGUS_SAMPLE_FP_UNIFORM: return options.quantifiers.sygusSampleFpUniform ? "true" : "false";
      case OptionEnum::SYGUS_SAMPLE_GRAMMAR: return options.quantifiers.sygusSampleGrammar ? "true" : "false";
      case OptionEnum::SYGUS_SAMPLES: return std::to_string(options.quantifiers.sygusSamples);
      case OptionEnum::SYGUS_SI: { std::stringstream s; s << options.quantifiers.cegqiSingleInvMode; return s.str(); }
      case OptionEnum::SYGUS_SI_ABORT: return options.quantifiers.cegqiSingleInvAbort ? "true" : "false";
      case OptionEnum::SYGUS_SI_RCONS: { std::stringstream s; s << options.quantifiers.cegqiSingleInvReconstruct; return s.str(); }
      case OptionEnum::SYGUS_SI_RCONS_LIMIT: return std::to_string(options.quantifiers.cegqiSingleInvReconstructLimit);
      case OptionEnum::SYGUS_SIMPLE_SYM_BREAK: { std::stringstream s; s << options.datatypes.sygusSimpleSymBreak; return s.str(); }
      case OptionEnum::SYGUS_STREAM: return options.quantifiers.sygusStream ? "true" : "false";
      case OptionEnum::SYGUS_SYM_BREAK_LAZY: return options.datatypes.sygusSymBreakLazy ? "true" : "false";
      case OptionEnum::SYGUS_SYM_BREAK_PBE: return options.datatypes.sygusSymBreakPbe ? "true" : "false";
      case OptionEnum::SYGUS_SYM_BREAK_RLV: return options.datatypes.sygusSymBreakRlv ? "true" : "false";
      case OptionEnum::SYGUS_UNIF_COND_INDEPENDENT_NO_REPEAT_SOL: return options.quantifiers.sygusUnifCondIndNoRepeatSol ? "true" : "false";
      case OptionEnum::SYGUS_UNIF_PI: { std::stringstream s; s << options.quantifiers.sygusUnifPi; return s.str(); }
      case OptionEnum::SYGUS_UNIF_SHUFFLE_COND: return options.quantifiers.sygusUnifShuffleCond ? "true" : "false";
      case OptionEnum::SYGUS_VERIFY_INST_MAX_ROUNDS: return std::to_string(options.quantifiers.sygusVerifyInstMaxRounds);
      case OptionEnum::SYGUS_VERIFY_TIMEOUT: return std::to_string(options.quantifiers.sygusVerifyTimeout);
      case OptionEnum::SYMMETRY_BREAKER: return options.uf.ufSymmetryBreaker ? "true" : "false";
      case OptionEnum::TC_MODE: { std::stringstream s; s << options.theory.tcMode; return s.str(); }
      case OptionEnum::TERM_DB_CD: return options.quantifiers.termDbCd ? "true" : "false";
      case OptionEnum::TERM_DB_MODE: { std::stringstream s; s << options.quantifiers.termDbMode; return s.str(); }
      case OptionEnum::THEORYOF_MODE: { std::stringstream s; s << options.theory.theoryOfMode; return s.str(); }
      case OptionEnum::TLIMIT: return std::to_string(options.base.cumulativeMillisecondLimit);
      case OptionEnum::TLIMIT_PER: return std::to_string(options.base.perCallMillisecondLimit);
      case OptionEnum::TRIGGER_ACTIVE_SEL: { std::stringstream s; s << options.quantifiers.triggerActiveSelMode; return s.str(); }
      case OptionEnum::TRIGGER_SEL: { std::stringstream s; s << options.quantifiers.triggerSelMode; return s.str(); }
      case OptionEnum::TYPE_CHECKING: return options.expr.typeChecking ? "true" : "false";
      case OptionEnum::UF_HO_EXT: return options.uf.ufHoExt ? "true" : "false";
      case OptionEnum::UF_LAZY_LL: return options.uf.ufHoLazyLambdaLift ? "true" : "false";
      case OptionEnum::UF_SS: { std::stringstream s; s << options.uf.ufssMode; return s.str(); }
      case OptionEnum::UF_SS_ABORT_CARD: return std::to_string(options.uf.ufssAbortCardinality);
      case OptionEnum::UF_SS_FAIR: return options.uf.ufssFairness ? "true" : "false";
      case OptionEnum::UF_SS_FAIR_MONOTONE: return options.uf.ufssFairnessMonotone ? "true" : "false";
      case OptionEnum::UNATE_LEMMAS: { std::stringstream s; s << options.arith.arithUnateLemmaMode; return s.str(); }
      case OptionEnum::UNCONSTRAINED_SIMP: return options.smt.unconstrainedSimp ? "true" : "false";
      case OptionEnum::UNSAT_CORES_MODE: { std::stringstream s; s << options.smt.unsatCoresMode; return s.str(); }
      case OptionEnum::USE_APPROX: return options.arith.useApprox ? "true" : "false";
      case OptionEnum::USE_FCSIMPLEX: return options.arith.useFC ? "true" : "false";
      case OptionEnum::USE_PORTFOLIO: return options.driver.usePortfolio ? "true" : "false";
      case OptionEnum::USE_SOI: return options.arith.useSOI ? "true" : "false";
      case OptionEnum::USER_PAT: { std::stringstream s; s << options.quantifiers.userPatternsQuant; return s.str(); }
      case OptionEnum::USER_POOL: { std::stringstream s; s << options.quantifiers.userPoolQuant; return s.str(); }
      case OptionEnum::VAR_ELIM_QUANT: return options.quantifiers.varElimQuant ? "true" : "false";
      case OptionEnum::VAR_INEQ_ELIM_QUANT: return options.quantifiers.varIneqElimQuant ? "true" : "false";
      case OptionEnum::VERBOSITY: return std::to_string(options.base.verbosity);
      case OptionEnum::VERSION: return options.driver.showVersion ? "true" : "false";
      case OptionEnum::WF_CHECKING: return options.expr.wellFormedChecking ? "true" : "false";
      case OptionEnum::WRITE_PARTITIONS_TO: { std::stringstream s; s << options.parallel.partitionsOut; return s.str(); }
      default:
      {
        throw OptionException("Ungettable option key or setting: " + name);
      }
    }
    // clang-format on
    throw OptionException("Unrecognized option key or setting: " + name);
  }

  void set(
      Options & opts, const std::string& name, const std::string& optionarg)
  {
    Trace("options") << "set option " << name << " = " << optionarg
                     << std::endl;
    // clang-format off
    auto it = NAME_TO_ENUM.find(name);
    if (it == NAME_TO_ENUM.end()) {
      throw OptionException("Unrecognized option key or setting: " + name);
    }
    switch (it->second) {
      case OptionEnum::ABSTRACT_VALUES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().abstractValues = value;
        opts.writeSmt().abstractValuesWasSetByUser = true;
        break;
      }
      case OptionEnum::ACKERMANN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().ackermann = value;
        opts.writeSmt().ackermannWasSetByUser = true;
        break;
      }
      case OptionEnum::APPEND_LEARNED_LITERALS_TO_CUBES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeParallel().appendLearnedLiteralsToCubes = value;
        opts.writeParallel().appendLearnedLiteralsToCubesWasSetByUser = true;
        break;
      }
      case OptionEnum::APPROX_BRANCH_DEPTH:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().maxApproxDepth = value;
        opts.writeArith().maxApproxDepthWasSetByUser = true;
        break;
      }
      case OptionEnum::ARITH_BRAB:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().brabTest = value;
        opts.writeArith().brabTestWasSetByUser = true;
        break;
      }
      case OptionEnum::ARITH_EQ_SOLVER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().arithEqSolver = value;
        opts.writeArith().arithEqSolverWasSetByUser = true;
        break;
      }
      case OptionEnum::ARITH_NO_PARTIAL_FUN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().arithNoPartialFun = value;
        opts.writeArith().arithNoPartialFunWasSetByUser = true;
        break;
      }
      case OptionEnum::ARITH_PROP:
      {
        auto value = stringToArithPropagationMode(optionarg);
        opts.writeArith().arithPropagationMode = value;
        opts.writeArith().arithPropagationModeWasSetByUser = true;
        break;
      }
      case OptionEnum::ARITH_PROP_CLAUSES:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().arithPropAsLemmaLength = value;
        opts.writeArith().arithPropAsLemmaLengthWasSetByUser = true;
        break;
      }
      case OptionEnum::ARITH_REWRITE_EQUALITIES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().arithRewriteEq = value;
        opts.writeArith().arithRewriteEqWasSetByUser = true;
        break;
      }
      case OptionEnum::ARITH_STATIC_LEARNING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().arithStaticLearning = value;
        opts.writeArith().arithStaticLearningWasSetByUser = true;
        break;
      }
      case OptionEnum::ARRAYS_EAGER_INDEX:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArrays().arraysEagerIndexSplitting = value;
        opts.writeArrays().arraysEagerIndexSplittingWasSetByUser = true;
        break;
      }
      case OptionEnum::ARRAYS_EAGER_LEMMAS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArrays().arraysEagerLemmas = value;
        opts.writeArrays().arraysEagerLemmasWasSetByUser = true;
        break;
      }
      case OptionEnum::ARRAYS_EXP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArrays().arraysExp = value;
        opts.writeArrays().arraysExpWasSetByUser = true;
        break;
      }
      case OptionEnum::ARRAYS_OPTIMIZE_LINEAR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArrays().arraysOptimizeLinear = value;
        opts.writeArrays().arraysOptimizeLinearWasSetByUser = true;
        break;
      }
      case OptionEnum::ARRAYS_PROP:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArrays().arraysPropagate = value;
        opts.writeArrays().arraysPropagateWasSetByUser = true;
        break;
      }
      case OptionEnum::ARRAYS_REDUCE_SHARING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArrays().arraysReduceSharing = value;
        opts.writeArrays().arraysReduceSharingWasSetByUser = true;
        break;
      }
      case OptionEnum::ARRAYS_WEAK_EQUIV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArrays().arraysWeakEquivalence = value;
        opts.writeArrays().arraysWeakEquivalenceWasSetByUser = true;
        break;
      }
      case OptionEnum::ASSIGN_FUNCTION_VALUES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeTheory().assignFunctionValues = value;
        opts.writeTheory().assignFunctionValuesWasSetByUser = true;
        break;
      }
      case OptionEnum::BITBLAST:
      {
        auto value = stringToBitblastMode(optionarg);
        opts.writeBv().bitblastMode = value;
        opts.writeBv().bitblastModeWasSetByUser = true;
        break;
      }
      case OptionEnum::BITWISE_EQ:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().bitwiseEq = value;
        opts.writeBv().bitwiseEqWasSetByUser = true;
        break;
      }
      case OptionEnum::BOOL_TO_BV:
      {
        auto value = stringToBoolToBVMode(optionarg);
        opts.writeBv().boolToBitvector = value;
        opts.writeBv().boolToBitvectorWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_ASSERT_INPUT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().bvAssertInput = value;
        opts.writeBv().bvAssertInputWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_EAGER_EVAL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().bvEagerEval = value;
        opts.writeBv().bvEagerEvalWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_GAUSS_ELIM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().bvGaussElim = value;
        opts.writeBv().bvGaussElimWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_INTRO_POW2:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().bvIntroducePow2 = value;
        opts.writeBv().bvIntroducePow2WasSetByUser = true;
        break;
      }
      case OptionEnum::BV_PRINT_CONSTS_AS_INDEXED_SYMBOLS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        ioutils::setDefaultBvPrintConstsAsIndexedSymbols(value);
        opts.writePrinter().bvPrintConstsAsIndexedSymbols = value;
        opts.writePrinter().bvPrintConstsAsIndexedSymbolsWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_PROPAGATE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().bitvectorPropagate = value;
        opts.writeBv().bitvectorPropagateWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_RW_EXTEND_EQ:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().rwExtendEq = value;
        opts.writeBv().rwExtendEqWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_SAT_SOLVER:
      {
        auto value = stringToSatSolverMode(optionarg);
        opts.handler().checkBvSatSolver(name, value);
        opts.writeBv().bvSatSolver = value;
        opts.writeBv().bvSatSolverWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_SOLVER:
      {
        auto value = stringToBVSolver(optionarg);
        opts.writeBv().bvSolver = value;
        opts.writeBv().bvSolverWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_TO_BOOL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBv().bitvectorToBool = value;
        opts.writeBv().bitvectorToBoolWasSetByUser = true;
        break;
      }
      case OptionEnum::BV_TO_INT_USE_POW2:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().bvToIntUsePow2 = value;
        opts.writeSmt().bvToIntUsePow2WasSetByUser = true;
        break;
      }
      case OptionEnum::BVAND_INTEGER_GRANULARITY:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.handler().checkMaximum(name, value, static_cast<uint64_t>(8));
        opts.writeSmt().BVAndIntegerGranularity = value;
        opts.writeSmt().BVAndIntegerGranularityWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().conflictBasedInst = value;
        opts.writeQuantifiers().conflictBasedInstWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI_ALL_CONFLICT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cbqiAllConflict = value;
        opts.writeQuantifiers().cbqiAllConflictWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI_EAGER_CHECK_RD:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cbqiEagerCheckRd = value;
        opts.writeQuantifiers().cbqiEagerCheckRdWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI_EAGER_TEST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cbqiEagerTest = value;
        opts.writeQuantifiers().cbqiEagerTestWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI_MODE:
      {
        auto value = stringToQcfMode(optionarg);
        opts.writeQuantifiers().cbqiMode = value;
        opts.writeQuantifiers().cbqiModeWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI_SKIP_RD:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cbqiSkipRd = value;
        opts.writeQuantifiers().cbqiSkipRdWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI_TCONSTRAINT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cbqiTConstraint = value;
        opts.writeQuantifiers().cbqiTConstraintWasSetByUser = true;
        break;
      }
      case OptionEnum::CBQI_VO_EXP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cbqiVoExp = value;
        opts.writeQuantifiers().cbqiVoExpWasSetByUser = true;
        break;
      }
      case OptionEnum::CDT_BISIMILAR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().cdtBisimilar = value;
        opts.writeDatatypes().cdtBisimilarWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGIS_SAMPLE:
      {
        auto value = stringToCegisSampleMode(optionarg);
        opts.writeQuantifiers().cegisSample = value;
        opts.writeQuantifiers().cegisSampleWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqi = value;
        opts.writeQuantifiers().cegqiWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_ALL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiAll = value;
        opts.writeQuantifiers().cegqiAllWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_BV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiBv = value;
        opts.writeQuantifiers().cegqiBvWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_BV_CONCAT_INV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiBvConcInv = value;
        opts.writeQuantifiers().cegqiBvConcInvWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_BV_INEQ:
      {
        auto value = stringToCegqiBvIneqMode(optionarg);
        opts.writeQuantifiers().cegqiBvIneqMode = value;
        opts.writeQuantifiers().cegqiBvIneqModeWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_BV_INTERLEAVE_VALUE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiBvInterleaveValue = value;
        opts.writeQuantifiers().cegqiBvInterleaveValueWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_BV_LINEAR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiBvLinearize = value;
        opts.writeQuantifiers().cegqiBvLinearizeWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_BV_RM_EXTRACT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiBvRmExtract = value;
        opts.writeQuantifiers().cegqiBvRmExtractWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_BV_SOLVE_NL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiBvSolveNl = value;
        opts.writeQuantifiers().cegqiBvSolveNlWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_FULL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiFullEffort = value;
        opts.writeQuantifiers().cegqiFullEffortWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_INF_INT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiUseInfInt = value;
        opts.writeQuantifiers().cegqiUseInfIntWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_INF_REAL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiUseInfReal = value;
        opts.writeQuantifiers().cegqiUseInfRealWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_INNERMOST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiInnermost = value;
        opts.writeQuantifiers().cegqiInnermostWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_MIDPOINT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiMidpoint = value;
        opts.writeQuantifiers().cegqiMidpointWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_MIN_BOUNDS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiMinBounds = value;
        opts.writeQuantifiers().cegqiMinBoundsWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_MULTI_INST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiMultiInst = value;
        opts.writeQuantifiers().cegqiMultiInstWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_NESTED_QE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiNestedQE = value;
        opts.writeQuantifiers().cegqiNestedQEWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_NOPT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiNopt = value;
        opts.writeQuantifiers().cegqiNoptWasSetByUser = true;
        break;
      }
      case OptionEnum::CEGQI_ROUND_UP_LIA:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiRoundUpLowerLia = value;
        opts.writeQuantifiers().cegqiRoundUpLowerLiaWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECK_ABDUCTS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().checkAbducts = value;
        opts.writeSmt().checkAbductsWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECK_INTERPOLANTS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().checkInterpolants = value;
        opts.writeSmt().checkInterpolantsWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECK_MODELS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().checkModels = value;
        opts.writeSmt().checkModelsWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECK_PROOF_STEPS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().checkProofSteps = value;
        opts.writeProof().checkProofStepsWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECK_PROOFS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().checkProofs = value;
        opts.writeSmt().checkProofsWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECK_SYNTH_SOL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().checkSynthSol = value;
        opts.writeSmt().checkSynthSolWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECK_UNSAT_CORES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().checkUnsatCores = value;
        opts.writeSmt().checkUnsatCoresWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECKS_BEFORE_PARTITION:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeParallel().checksBeforePartitioning = value;
        opts.writeParallel().checksBeforePartitioningWasSetByUser = true;
        break;
      }
      case OptionEnum::CHECKS_BETWEEN_PARTITIONS:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeParallel().checksBetweenPartitions = value;
        opts.writeParallel().checksBetweenPartitionsWasSetByUser = true;
        break;
      }
      case OptionEnum::COLLECT_PIVOT_STATS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().collectPivots = value;
        opts.writeArith().collectPivotsWasSetByUser = true;
        break;
      }
      case OptionEnum::COMPUTE_PARTITIONS:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeParallel().computePartitions = value;
        opts.writeParallel().computePartitionsWasSetByUser = true;
        break;
      }
      case OptionEnum::COND_VAR_SPLIT_QUANT:
      {
        auto value = stringToCondVarSplitQuantMode(optionarg);
        opts.writeQuantifiers().condVarSplitQuant = value;
        opts.writeQuantifiers().condVarSplitQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::CONDENSE_FUNCTION_VALUES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeTheory().condenseFunctionValues = value;
        opts.writeTheory().condenseFunctionValuesWasSetByUser = true;
        break;
      }
      case OptionEnum::CONJECTURE_GEN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().conjectureGen = value;
        opts.writeQuantifiers().conjectureGenWasSetByUser = true;
        break;
      }
      case OptionEnum::CONJECTURE_GEN_GT_ENUM:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().conjectureGenGtEnum = value;
        opts.writeQuantifiers().conjectureGenGtEnumWasSetByUser = true;
        break;
      }
      case OptionEnum::CONJECTURE_GEN_MAX_DEPTH:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().conjectureGenMaxDepth = value;
        opts.writeQuantifiers().conjectureGenMaxDepthWasSetByUser = true;
        break;
      }
      case OptionEnum::CONJECTURE_GEN_PER_ROUND:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().conjectureGenPerRound = value;
        opts.writeQuantifiers().conjectureGenPerRoundWasSetByUser = true;
        break;
      }
      case OptionEnum::CONS_EXP_TRIGGERS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().consExpandTriggers = value;
        opts.writeQuantifiers().consExpandTriggersWasSetByUser = true;
        break;
      }
      case OptionEnum::COPYRIGHT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().showCopyright(name, value);
        opts.writeDriver().showCopyright = value;
        opts.writeDriver().showCopyrightWasSetByUser = true;
        break;
      }
      case OptionEnum::CUT_ALL_BOUNDED:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().doCutAllBounded = value;
        opts.writeArith().doCutAllBoundedWasSetByUser = true;
        break;
      }
      case OptionEnum::DAG_THRESH:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.handler().checkMinimum(name, value, static_cast<int64_t>(0));
        ioutils::setDefaultDagThresh(value);
        opts.writePrinter().dagThresh = value;
        opts.writePrinter().dagThreshWasSetByUser = true;
        break;
      }
      case OptionEnum::DEBUG_CHECK_MODELS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().debugCheckModels = value;
        opts.writeSmt().debugCheckModelsWasSetByUser = true;
        break;
      }
      case OptionEnum::DECISION:
      {
        auto value = stringToDecisionMode(optionarg);
        opts.writeDecision().decisionMode = value;
        opts.writeDecision().decisionModeWasSetByUser = true;
        break;
      }
      case OptionEnum::DEEP_RESTART:
      {
        auto value = stringToDeepRestartMode(optionarg);
        opts.writeSmt().deepRestartMode = value;
        opts.writeSmt().deepRestartModeWasSetByUser = true;
        break;
      }
      case OptionEnum::DEEP_RESTART_FACTOR:
      {
        auto value = handlers::handleOption<double>(name, optionarg);
        opts.handler().checkMinimum(name, value, static_cast<double>(0.0));
        opts.handler().checkMaximum(name, value, static_cast<double>(1000.0));
        opts.writeSmt().deepRestartFactor = value;
        opts.writeSmt().deepRestartFactorWasSetByUser = true;
        break;
      }
      case OptionEnum::DIFFICULTY_MODE:
      {
        auto value = stringToDifficultyMode(optionarg);
        opts.writeSmt().difficultyMode = value;
        opts.writeSmt().difficultyModeWasSetByUser = true;
        break;
      }
      case OptionEnum::DIO_DECOMPS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().exportDioDecompositions = value;
        opts.writeArith().exportDioDecompositionsWasSetByUser = true;
        break;
      }
      case OptionEnum::DIO_SOLVER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().arithDioSolver = value;
        opts.writeArith().arithDioSolverWasSetByUser = true;
        break;
      }
      case OptionEnum::DIO_TURNS:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().dioSolverTurns = value;
        opts.writeArith().dioSolverTurnsWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_BINARY_SPLIT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().dtBinarySplit = value;
        opts.writeDatatypes().dtBinarySplitWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_BLAST_SPLITS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().dtBlastSplits = value;
        opts.writeDatatypes().dtBlastSplitsWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_CYCLIC:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().dtCyclic = value;
        opts.writeDatatypes().dtCyclicWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_INFER_AS_LEMMAS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().dtInferAsLemmas = value;
        opts.writeDatatypes().dtInferAsLemmasWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_NESTED_REC:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().dtNestedRec = value;
        opts.writeDatatypes().dtNestedRecWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_POLITE_OPTIMIZE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().dtPoliteOptimize = value;
        opts.writeDatatypes().dtPoliteOptimizeWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_SHARE_SEL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().dtSharedSelectors = value;
        opts.writeDatatypes().dtSharedSelectorsWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_STC_IND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().dtStcInduction = value;
        opts.writeQuantifiers().dtStcInductionWasSetByUser = true;
        break;
      }
      case OptionEnum::DT_VAR_EXP_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().dtVarExpandQuant = value;
        opts.writeQuantifiers().dtVarExpandQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::DUMP_DIFFICULTY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().dumpDifficulty = value;
        opts.writeDriver().dumpDifficultyWasSetByUser = true;
        break;
      }
      case OptionEnum::DUMP_INSTANTIATIONS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().dumpInstantiations = value;
        opts.writeDriver().dumpInstantiationsWasSetByUser = true;
        break;
      }
      case OptionEnum::DUMP_INSTANTIATIONS_DEBUG:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().dumpInstantiationsDebug = value;
        opts.writeDriver().dumpInstantiationsDebugWasSetByUser = true;
        break;
      }
      case OptionEnum::DUMP_MODELS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().dumpModels = value;
        opts.writeDriver().dumpModelsWasSetByUser = true;
        break;
      }
      case OptionEnum::DUMP_PROOFS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().dumpProofs = value;
        opts.writeDriver().dumpProofsWasSetByUser = true;
        break;
      }
      case OptionEnum::DUMP_UNSAT_CORES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().dumpUnsatCores = value;
        opts.writeDriver().dumpUnsatCoresWasSetByUser = true;
        break;
      }
      case OptionEnum::E_MATCHING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().eMatching = value;
        opts.writeQuantifiers().eMatchingWasSetByUser = true;
        break;
      }
      case OptionEnum::EAGER_ARITH_BV_CONV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeUf().eagerArithBvConv = value;
        opts.writeUf().eagerArithBvConvWasSetByUser = true;
        break;
      }
      case OptionEnum::EARLY_EXIT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().earlyExit = value;
        opts.writeDriver().earlyExitWasSetByUser = true;
        break;
      }
      case OptionEnum::EARLY_ITE_REMOVAL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().earlyIteRemoval = value;
        opts.writeSmt().earlyIteRemovalWasSetByUser = true;
        break;
      }
      case OptionEnum::EE_MODE:
      {
        auto value = stringToEqEngineMode(optionarg);
        opts.writeTheory().eeMode = value;
        opts.writeTheory().eeModeWasSetByUser = true;
        break;
      }
      case OptionEnum::ELIM_TAUT_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().elimTautQuant = value;
        opts.writeQuantifiers().elimTautQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::ENUM_INST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().enumInst = value;
        opts.writeQuantifiers().enumInstWasSetByUser = true;
        break;
      }
      case OptionEnum::ENUM_INST_INTERLEAVE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().enumInstInterleave = value;
        opts.writeQuantifiers().enumInstInterleaveWasSetByUser = true;
        break;
      }
      case OptionEnum::ENUM_INST_LIMIT:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().enumInstLimit = value;
        opts.writeQuantifiers().enumInstLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::ENUM_INST_RD:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().enumInstRd = value;
        opts.writeQuantifiers().enumInstRdWasSetByUser = true;
        break;
      }
      case OptionEnum::ENUM_INST_STRATIFY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().enumInstStratify = value;
        opts.writeQuantifiers().enumInstStratifyWasSetByUser = true;
        break;
      }
      case OptionEnum::ENUM_INST_SUM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().enumInstSum = value;
        opts.writeQuantifiers().enumInstSumWasSetByUser = true;
        break;
      }
      case OptionEnum::ERR:
      {
        auto value = handlers::handleOption<ManagedErr>(name, optionarg);
        opts.handler().setErrStream(name, value);
        opts.writeBase().err = value;
        opts.writeBase().errWasSetByUser = true;
        break;
      }
      case OptionEnum::ERROR_SELECTION_RULE:
      {
        auto value = stringToErrorSelectionRule(optionarg);
        opts.writeArith().arithErrorSelectionRule = value;
        opts.writeArith().arithErrorSelectionRuleWasSetByUser = true;
        break;
      }
      case OptionEnum::EXPR_DEPTH:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.handler().checkMinimum(name, value, static_cast<int64_t>(-1));
        ioutils::setDefaultNodeDepth(value);
        opts.writePrinter().nodeDepth = value;
        opts.writePrinter().nodeDepthWasSetByUser = true;
        break;
      }
      case OptionEnum::EXT_REW_PREP:
      {
        auto value = stringToExtRewPrepMode(optionarg);
        opts.writeSmt().extRewPrep = value;
        opts.writeSmt().extRewPrepWasSetByUser = true;
        break;
      }
      case OptionEnum::EXT_REWRITE_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().extRewriteQuant = value;
        opts.writeQuantifiers().extRewriteQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::FC_PENALTIES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().havePenalties = value;
        opts.writeArith().havePenaltiesWasSetByUser = true;
        break;
      }
      case OptionEnum::FF_FIELD_POLYS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeFf().ffFieldPolys = value;
        opts.writeFf().ffFieldPolysWasSetByUser = true;
        break;
      }
      case OptionEnum::FF_TRACE_GB:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeFf().ffTraceGb = value;
        opts.writeFf().ffTraceGbWasSetByUser = true;
        break;
      }
      case OptionEnum::FILENAME:
      {
        auto value = handlers::handleOption<std::string>(name, optionarg);
        opts.writeDriver().filename = value;
        opts.writeDriver().filenameWasSetByUser = true;
        break;
      }
      case OptionEnum::FILESYSTEM_ACCESS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeParser().filesystemAccess = value;
        opts.writeParser().filesystemAccessWasSetByUser = true;
        break;
      }
      case OptionEnum::FINITE_MODEL_FIND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().finiteModelFind = value;
        opts.writeQuantifiers().finiteModelFindWasSetByUser = true;
        break;
      }
      case OptionEnum::FLATTEN_HO_CHAINS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        ioutils::setDefaultFlattenHOChains(value);
        opts.writePrinter().flattenHOChains = value;
        opts.writePrinter().flattenHOChainsWasSetByUser = true;
        break;
      }
      case OptionEnum::FLEX_PARSER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeParser().flexParser = value;
        opts.writeParser().flexParserWasSetByUser = true;
        break;
      }
      case OptionEnum::FMF_BOUND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().fmfBound = value;
        opts.writeQuantifiers().fmfBoundWasSetByUser = true;
        break;
      }
      case OptionEnum::FMF_BOUND_BLAST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().fmfBoundBlast = value;
        opts.writeQuantifiers().fmfBoundBlastWasSetByUser = true;
        break;
      }
      case OptionEnum::FMF_BOUND_LAZY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().fmfBoundLazy = value;
        opts.writeQuantifiers().fmfBoundLazyWasSetByUser = true;
        break;
      }
      case OptionEnum::FMF_FUN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().fmfFunWellDefined = value;
        opts.writeQuantifiers().fmfFunWellDefinedWasSetByUser = true;
        break;
      }
      case OptionEnum::FMF_FUN_RLV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().fmfFunWellDefinedRelevant = value;
        opts.writeQuantifiers().fmfFunWellDefinedRelevantWasSetByUser = true;
        break;
      }
      case OptionEnum::FMF_MBQI:
      {
        auto value = stringToFmfMbqiMode(optionarg);
        opts.writeQuantifiers().fmfMbqiMode = value;
        opts.writeQuantifiers().fmfMbqiModeWasSetByUser = true;
        break;
      }
      case OptionEnum::FMF_TYPE_COMPLETION_THRESH:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().fmfTypeCompletionThresh = value;
        opts.writeQuantifiers().fmfTypeCompletionThreshWasSetByUser = true;
        break;
      }
      case OptionEnum::FORCE_LOGIC:
      {
        auto value = handlers::handleOption<std::string>(name, optionarg);
        opts.writeParser().forceLogicString = value;
        opts.writeParser().forceLogicStringWasSetByUser = true;
        break;
      }
      case OptionEnum::FORCE_NO_LIMIT_CPU_WHILE_DUMP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().forceNoLimitCpuWhileDump = value;
        opts.writeDriver().forceNoLimitCpuWhileDumpWasSetByUser = true;
        break;
      }
      case OptionEnum::FOREIGN_THEORY_REWRITE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().foreignTheoryRewrite = value;
        opts.writeSmt().foreignTheoryRewriteWasSetByUser = true;
        break;
      }
      case OptionEnum::FP_EXP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeFp().fpExp = value;
        opts.writeFp().fpExpWasSetByUser = true;
        break;
      }
      case OptionEnum::FP_LAZY_WB:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeFp().fpLazyWb = value;
        opts.writeFp().fpLazyWbWasSetByUser = true;
        break;
      }
      case OptionEnum::FULL_SATURATE_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().fullSaturateQuant = value;
        opts.writeQuantifiers().fullSaturateQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::GLOBAL_DECLARATIONS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeParser().globalDeclarations = value;
        opts.writeParser().globalDeclarationsWasSetByUser = true;
        break;
      }
      case OptionEnum::GLOBAL_NEGATE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().globalNegate = value;
        opts.writeQuantifiers().globalNegateWasSetByUser = true;
        break;
      }
      case OptionEnum::HELP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().help = value;
        opts.writeDriver().helpWasSetByUser = true;
        break;
      }
      case OptionEnum::HEURISTIC_PIVOTS:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().arithHeuristicPivots = value;
        opts.writeArith().arithHeuristicPivotsWasSetByUser = true;
        break;
      }
      case OptionEnum::HO_ELIM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().hoElim = value;
        opts.writeQuantifiers().hoElimWasSetByUser = true;
        break;
      }
      case OptionEnum::HO_ELIM_STORE_AX:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().hoElimStoreAx = value;
        opts.writeQuantifiers().hoElimStoreAxWasSetByUser = true;
        break;
      }
      case OptionEnum::HO_MATCHING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().hoMatching = value;
        opts.writeQuantifiers().hoMatchingWasSetByUser = true;
        break;
      }
      case OptionEnum::HO_MERGE_TERM_DB:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().hoMergeTermDb = value;
        opts.writeQuantifiers().hoMergeTermDbWasSetByUser = true;
        break;
      }
      case OptionEnum::IAND_MODE:
      {
        auto value = stringToIandMode(optionarg);
        opts.writeSmt().iandMode = value;
        opts.writeSmt().iandModeWasSetByUser = true;
        break;
      }
      case OptionEnum::IEVAL:
      {
        auto value = stringToIevalMode(optionarg);
        opts.writeQuantifiers().ievalMode = value;
        opts.writeQuantifiers().ievalModeWasSetByUser = true;
        break;
      }
      case OptionEnum::IN:
      {
        auto value = handlers::handleOption<ManagedIn>(name, optionarg);
        opts.writeBase().in = value;
        opts.writeBase().inWasSetByUser = true;
        break;
      }
      case OptionEnum::INCREMENT_TRIGGERS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().incrementTriggers = value;
        opts.writeQuantifiers().incrementTriggersWasSetByUser = true;
        break;
      }
      case OptionEnum::INCREMENTAL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBase().incrementalSolving = value;
        opts.writeBase().incrementalSolvingWasSetByUser = true;
        break;
      }
      case OptionEnum::INST_MAX_LEVEL:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().instMaxLevel = value;
        opts.writeQuantifiers().instMaxLevelWasSetByUser = true;
        break;
      }
      case OptionEnum::INST_MAX_ROUNDS:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().instMaxRounds = value;
        opts.writeQuantifiers().instMaxRoundsWasSetByUser = true;
        break;
      }
      case OptionEnum::INST_NO_ENTAIL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().instNoEntail = value;
        opts.writeQuantifiers().instNoEntailWasSetByUser = true;
        break;
      }
      case OptionEnum::INST_WHEN:
      {
        auto value = stringToInstWhenMode(optionarg);
        opts.writeQuantifiers().instWhenMode = value;
        opts.writeQuantifiers().instWhenModeWasSetByUser = true;
        break;
      }
      case OptionEnum::INST_WHEN_PHASE:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().instWhenPhase = value;
        opts.writeQuantifiers().instWhenPhaseWasSetByUser = true;
        break;
      }
      case OptionEnum::INT_WF_IND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().intWfInduction = value;
        opts.writeQuantifiers().intWfInductionWasSetByUser = true;
        break;
      }
      case OptionEnum::INTERACTIVE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().interactive = value;
        opts.writeDriver().interactiveWasSetByUser = true;
        break;
      }
      case OptionEnum::INTERPOLANTS_MODE:
      {
        auto value = stringToInterpolantsMode(optionarg);
        opts.writeSmt().interpolantsMode = value;
        opts.writeSmt().interpolantsModeWasSetByUser = true;
        break;
      }
      case OptionEnum::ITE_DTT_SPLIT_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().iteDtTesterSplitQuant = value;
        opts.writeQuantifiers().iteDtTesterSplitQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::ITE_LIFT_QUANT:
      {
        auto value = stringToIteLiftQuantMode(optionarg);
        opts.writeQuantifiers().iteLiftQuant = value;
        opts.writeQuantifiers().iteLiftQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::ITE_SIMP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().doITESimp = value;
        opts.writeSmt().doITESimpWasSetByUser = true;
        break;
      }
      case OptionEnum::JH_RLV_ORDER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDecision().jhRlvOrder = value;
        opts.writeDecision().jhRlvOrderWasSetByUser = true;
        break;
      }
      case OptionEnum::JH_SKOLEM:
      {
        auto value = stringToJutificationSkolemMode(optionarg);
        opts.writeDecision().jhSkolemMode = value;
        opts.writeDecision().jhSkolemModeWasSetByUser = true;
        break;
      }
      case OptionEnum::JH_SKOLEM_RLV:
      {
        auto value = stringToJutificationSkolemRlvMode(optionarg);
        opts.writeDecision().jhSkolemRlvMode = value;
        opts.writeDecision().jhSkolemRlvModeWasSetByUser = true;
        break;
      }
      case OptionEnum::LANG:
      {
        auto value = opts.handler().stringToLanguage(name, optionarg);
        opts.handler().setInputLanguage(name, value);
        opts.writeBase().inputLanguage = value;
        opts.writeBase().inputLanguageWasSetByUser = true;
        break;
      }
      case OptionEnum::LEARNED_REWRITE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().learnedRewrite = value;
        opts.writeSmt().learnedRewriteWasSetByUser = true;
        break;
      }
      case OptionEnum::LEMMAS_ON_REPLAY_FAILURE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().replayFailureLemma = value;
        opts.writeArith().replayFailureLemmaWasSetByUser = true;
        break;
      }
      case OptionEnum::LFSC_EXPAND_TRUST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().lfscExpandTrust = value;
        opts.writeProof().lfscExpandTrustWasSetByUser = true;
        break;
      }
      case OptionEnum::LFSC_FLATTEN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().lfscFlatten = value;
        opts.writeProof().lfscFlattenWasSetByUser = true;
        break;
      }
      case OptionEnum::LITERAL_MATCHING:
      {
        auto value = stringToLiteralMatchMode(optionarg);
        opts.writeQuantifiers().literalMatchMode = value;
        opts.writeQuantifiers().literalMatchModeWasSetByUser = true;
        break;
      }
      case OptionEnum::MACROS_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().macrosQuant = value;
        opts.writeQuantifiers().macrosQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::MACROS_QUANT_MODE:
      {
        auto value = stringToMacrosQuantMode(optionarg);
        opts.writeQuantifiers().macrosQuantMode = value;
        opts.writeQuantifiers().macrosQuantModeWasSetByUser = true;
        break;
      }
      case OptionEnum::MAXCUTSINCONTEXT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().maxCutsInContext = value;
        opts.writeArith().maxCutsInContextWasSetByUser = true;
        break;
      }
      case OptionEnum::MBQI:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().mbqi = value;
        opts.writeQuantifiers().mbqiWasSetByUser = true;
        break;
      }
      case OptionEnum::MBQI_INTERLEAVE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().mbqiInterleave = value;
        opts.writeQuantifiers().mbqiInterleaveWasSetByUser = true;
        break;
      }
      case OptionEnum::MBQI_ONE_INST_PER_ROUND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().fmfOneInstPerRound = value;
        opts.writeQuantifiers().fmfOneInstPerRoundWasSetByUser = true;
        break;
      }
      case OptionEnum::MINIMAL_UNSAT_CORES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().minimalUnsatCores = value;
        opts.writeSmt().minimalUnsatCoresWasSetByUser = true;
        break;
      }
      case OptionEnum::MINISAT_DUMP_DIMACS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProp().minisatDumpDimacs = value;
        opts.writeProp().minisatDumpDimacsWasSetByUser = true;
        break;
      }
      case OptionEnum::MINISAT_SIMPLIFICATION:
      {
        auto value = stringToMinisatSimpMode(optionarg);
        opts.writeProp().minisatSimpMode = value;
        opts.writeProp().minisatSimpModeWasSetByUser = true;
        break;
      }
      case OptionEnum::MINISCOPE_QUANT:
      {
        auto value = stringToMiniscopeQuantMode(optionarg);
        opts.writeQuantifiers().miniscopeQuant = value;
        opts.writeQuantifiers().miniscopeQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::MIPLIB_TRICK:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().arithMLTrick = value;
        opts.writeArith().arithMLTrickWasSetByUser = true;
        break;
      }
      case OptionEnum::MIPLIB_TRICK_SUBS:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().arithMLTrickSubstitutions = value;
        opts.writeArith().arithMLTrickSubstitutionsWasSetByUser = true;
        break;
      }
      case OptionEnum::MODEL_CORES:
      {
        auto value = stringToModelCoresMode(optionarg);
        opts.writeSmt().modelCoresMode = value;
        opts.writeSmt().modelCoresModeWasSetByUser = true;
        break;
      }
      case OptionEnum::MODEL_U_PRINT:
      {
        auto value = stringToModelUninterpPrintMode(optionarg);
        ioutils::setDefaultModelUninterpPrint(value);
        opts.writePrinter().modelUninterpPrint = value;
        opts.writePrinter().modelUninterpPrintWasSetByUser = true;
        break;
      }
      case OptionEnum::MODEL_VAR_ELIM_UNEVAL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().modelVarElimUneval = value;
        opts.writeSmt().modelVarElimUnevalWasSetByUser = true;
        break;
      }
      case OptionEnum::MULTI_TRIGGER_CACHE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().multiTriggerCache = value;
        opts.writeQuantifiers().multiTriggerCacheWasSetByUser = true;
        break;
      }
      case OptionEnum::MULTI_TRIGGER_LINEAR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().multiTriggerLinear = value;
        opts.writeQuantifiers().multiTriggerLinearWasSetByUser = true;
        break;
      }
      case OptionEnum::MULTI_TRIGGER_PRIORITY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().multiTriggerPriority = value;
        opts.writeQuantifiers().multiTriggerPriorityWasSetByUser = true;
        break;
      }
      case OptionEnum::MULTI_TRIGGER_WHEN_SINGLE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().multiTriggerWhenSingle = value;
        opts.writeQuantifiers().multiTriggerWhenSingleWasSetByUser = true;
        break;
      }
      case OptionEnum::NEW_PROP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().newProp = value;
        opts.writeArith().newPropWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_COV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlCov = value;
        opts.writeArith().nlCovWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_COV_FORCE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlCovForce = value;
        opts.writeArith().nlCovForceWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_COV_LIFT:
      {
        auto value = stringTonlCovLiftingMode(optionarg);
        opts.writeArith().nlCovLifting = value;
        opts.writeArith().nlCovLiftingWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_COV_LINEAR_MODEL:
      {
        auto value = stringTonlCovLinearModelMode(optionarg);
        opts.writeArith().nlCovLinearModel = value;
        opts.writeArith().nlCovLinearModelWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_COV_PROJ:
      {
        auto value = stringTonlCovProjectionMode(optionarg);
        opts.writeArith().nlCovProjection = value;
        opts.writeArith().nlCovProjectionWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_COV_PRUNE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlCovPrune = value;
        opts.writeArith().nlCovPruneWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_COV_VAR_ELIM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlCovVarElim = value;
        opts.writeArith().nlCovVarElimWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT:
      {
        auto value = stringToNlExtMode(optionarg);
        opts.writeArith().nlExt = value;
        opts.writeArith().nlExtWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_ENT_CONF:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtEntailConflicts = value;
        opts.writeArith().nlExtEntailConflictsWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_FACTOR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtFactor = value;
        opts.writeArith().nlExtFactorWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_INC_PREC:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtIncPrecision = value;
        opts.writeArith().nlExtIncPrecisionWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_PURIFY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtPurify = value;
        opts.writeArith().nlExtPurifyWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_RBOUND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtResBound = value;
        opts.writeArith().nlExtResBoundWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_REWRITE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtRewrites = value;
        opts.writeArith().nlExtRewritesWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_SPLIT_ZERO:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtSplitZero = value;
        opts.writeArith().nlExtSplitZeroWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_TF_TAYLOR_DEG:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().nlExtTfTaylorDegree = value;
        opts.writeArith().nlExtTfTaylorDegreeWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_TF_TPLANES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtTfTangentPlanes = value;
        opts.writeArith().nlExtTfTangentPlanesWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_TPLANES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtTangentPlanes = value;
        opts.writeArith().nlExtTangentPlanesWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_EXT_TPLANES_INTERLEAVE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlExtTangentPlanesInterleave = value;
        opts.writeArith().nlExtTangentPlanesInterleaveWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_ICP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlICP = value;
        opts.writeArith().nlICPWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_RLV:
      {
        auto value = stringToNlRlvMode(optionarg);
        opts.writeArith().nlRlvMode = value;
        opts.writeArith().nlRlvModeWasSetByUser = true;
        break;
      }
      case OptionEnum::NL_RLV_ASSERT_BOUNDS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().nlRlvAssertBounds = value;
        opts.writeArith().nlRlvAssertBoundsWasSetByUser = true;
        break;
      }
      case OptionEnum::ON_REPEAT_ITE_SIMP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().doITESimpOnRepeat = value;
        opts.writeSmt().doITESimpOnRepeatWasSetByUser = true;
        break;
      }
      case OptionEnum::OPT_RES_RECONSTRUCTION_SIZE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().optResReconSize = value;
        opts.writeProof().optResReconSizeWasSetByUser = true;
        break;
      }
      case OptionEnum::ORACLES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().oracles = value;
        opts.writeQuantifiers().oraclesWasSetByUser = true;
        break;
      }
      case OptionEnum::OUT:
      {
        auto value = handlers::handleOption<ManagedOut>(name, optionarg);
        opts.writeBase().out = value;
        opts.writeBase().outWasSetByUser = true;
        break;
      }
      case OptionEnum::OUTPUT:
      {
        auto value = stringToOutputTag(optionarg);
        opts.handler().enableOutputTag(name, value);
        break;
      }
      case OptionEnum::OUTPUT_LANG:
      {
        auto value = opts.handler().stringToLanguage(name, optionarg);
        ioutils::setDefaultOutputLanguage(value);
        opts.writePrinter().outputLanguage = value;
        opts.writePrinter().outputLanguageWasSetByUser = true;
        break;
      }
      case OptionEnum::PARSE_ONLY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBase().parseOnly = value;
        opts.writeBase().parseOnlyWasSetByUser = true;
        break;
      }
      case OptionEnum::PARTIAL_TRIGGERS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().partialTriggers = value;
        opts.writeQuantifiers().partialTriggersWasSetByUser = true;
        break;
      }
      case OptionEnum::PARTITION_CHECK:
      {
        auto value = stringToCheckMode(optionarg);
        opts.writeParallel().partitionCheck = value;
        opts.writeParallel().partitionCheckWasSetByUser = true;
        break;
      }
      case OptionEnum::PARTITION_CONFLICT_SIZE:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeParallel().partitionConflictSize = value;
        opts.writeParallel().partitionConflictSizeWasSetByUser = true;
        break;
      }
      case OptionEnum::PARTITION_STRATEGY:
      {
        auto value = stringToPartitionMode(optionarg);
        opts.writeParallel().partitionStrategy = value;
        opts.writeParallel().partitionStrategyWasSetByUser = true;
        break;
      }
      case OptionEnum::PB_REWRITES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().pbRewrites = value;
        opts.writeArith().pbRewritesWasSetByUser = true;
        break;
      }
      case OptionEnum::PIVOT_THRESHOLD:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().arithPivotThreshold = value;
        opts.writeArith().arithPivotThresholdWasSetByUser = true;
        break;
      }
      case OptionEnum::POOL_INST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().poolInst = value;
        opts.writeQuantifiers().poolInstWasSetByUser = true;
        break;
      }
      case OptionEnum::PORTFOLIO_JOBS:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeDriver().portfolioJobs = value;
        opts.writeDriver().portfolioJobsWasSetByUser = true;
        break;
      }
      case OptionEnum::PP_ASSERT_MAX_SUB_SIZE:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().ppAssertMaxSubSize = value;
        opts.writeArith().ppAssertMaxSubSizeWasSetByUser = true;
        break;
      }
      case OptionEnum::PRE_SKOLEM_QUANT:
      {
        auto value = stringToPreSkolemQuantMode(optionarg);
        opts.writeQuantifiers().preSkolemQuant = value;
        opts.writeQuantifiers().preSkolemQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::PRE_SKOLEM_QUANT_NESTED:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().preSkolemQuantNested = value;
        opts.writeQuantifiers().preSkolemQuantNestedWasSetByUser = true;
        break;
      }
      case OptionEnum::PRENEX_QUANT:
      {
        auto value = stringToPrenexQuantMode(optionarg);
        opts.writeQuantifiers().prenexQuant = value;
        opts.writeQuantifiers().prenexQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::PRENEX_QUANT_USER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().prenexQuantUser = value;
        opts.writeQuantifiers().prenexQuantUserWasSetByUser = true;
        break;
      }
      case OptionEnum::PREPROCESS_ONLY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeBase().preprocessOnly = value;
        opts.writeBase().preprocessOnlyWasSetByUser = true;
        break;
      }
      case OptionEnum::PREREGISTER_MODE:
      {
        auto value = stringToPreRegisterMode(optionarg);
        opts.writeProp().preRegisterMode = value;
        opts.writeProp().preRegisterModeWasSetByUser = true;
        break;
      }
      case OptionEnum::PRINT_DOT_CLUSTERS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().printDotClusters = value;
        opts.writeProof().printDotClustersWasSetByUser = true;
        break;
      }
      case OptionEnum::PRINT_INST:
      {
        auto value = stringToPrintInstMode(optionarg);
        opts.writeQuantifiers().printInstMode = value;
        opts.writeQuantifiers().printInstModeWasSetByUser = true;
        break;
      }
      case OptionEnum::PRINT_INST_FULL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().printInstFull = value;
        opts.writeQuantifiers().printInstFullWasSetByUser = true;
        break;
      }
      case OptionEnum::PRINT_SUCCESS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().printSuccess = value;
        opts.writeDriver().printSuccessWasSetByUser = true;
        break;
      }
      case OptionEnum::PRINT_UNSAT_CORES_FULL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().printUnsatCoresFull = value;
        opts.writeSmt().printUnsatCoresFullWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_ABDUCTS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceAbducts = value;
        opts.writeSmt().produceAbductsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_ASSERTIONS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceAssertions = value;
        opts.writeSmt().produceAssertionsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_ASSIGNMENTS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceAssignments = value;
        opts.writeSmt().produceAssignmentsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_DIFFICULTY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceDifficulty = value;
        opts.writeSmt().produceDifficultyWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_INTERPOLANTS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceInterpolants = value;
        opts.writeSmt().produceInterpolantsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_LEARNED_LITERALS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceLearnedLiterals = value;
        opts.writeSmt().produceLearnedLiteralsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_MODELS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceModels = value;
        opts.writeSmt().produceModelsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_PROOFS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceProofs = value;
        opts.writeSmt().produceProofsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_UNSAT_ASSUMPTIONS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().unsatAssumptions = value;
        opts.writeSmt().unsatAssumptionsWasSetByUser = true;
        break;
      }
      case OptionEnum::PRODUCE_UNSAT_CORES:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().produceUnsatCores = value;
        opts.writeSmt().produceUnsatCoresWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_ALETHE_RES_PIVOTS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().proofAletheResPivots = value;
        opts.writeProof().proofAletheResPivotsWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_ANNOTATE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().proofAnnotate = value;
        opts.writeProof().proofAnnotateWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_CHECK:
      {
        auto value = stringToProofCheckMode(optionarg);
        opts.writeProof().proofCheck = value;
        opts.writeProof().proofCheckWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_DOT_DAG:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().printDotAsDAG = value;
        opts.writeProof().printDotAsDAGWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_FORMAT_MODE:
      {
        auto value = stringToProofFormatMode(optionarg);
        opts.writeProof().proofFormatMode = value;
        opts.writeProof().proofFormatModeWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_GRANULARITY:
      {
        auto value = stringToProofGranularityMode(optionarg);
        opts.writeProof().proofGranularityMode = value;
        opts.writeProof().proofGranularityModeWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_MODE:
      {
        auto value = stringToProofMode(optionarg);
        opts.writeSmt().proofMode = value;
        opts.writeSmt().proofModeWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_PEDANTIC:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.handler().checkMaximum(name, value, static_cast<uint64_t>(100));
        opts.writeProof().proofPedantic = value;
        opts.writeProof().proofPedanticWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_PP_MERGE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().proofPpMerge = value;
        opts.writeProof().proofPpMergeWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_PRINT_CONCLUSION:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().proofPrintConclusion = value;
        opts.writeProof().proofPrintConclusionWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_PRUNE_INPUT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeProof().proofPruneInput = value;
        opts.writeProof().proofPruneInputWasSetByUser = true;
        break;
      }
      case OptionEnum::PROOF_REWRITE_RCONS_LIMIT:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeProof().proofRewriteRconsRecLimit = value;
        opts.writeProof().proofRewriteRconsRecLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::PROP_ROW_LENGTH:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().arithPropagateMaxLength = value;
        opts.writeArith().arithPropagateMaxLengthWasSetByUser = true;
        break;
      }
      case OptionEnum::PURIFY_TRIGGERS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().purifyTriggers = value;
        opts.writeQuantifiers().purifyTriggersWasSetByUser = true;
        break;
      }
      case OptionEnum::QUANT_ALPHA_EQUIV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().quantAlphaEquiv = value;
        opts.writeQuantifiers().quantAlphaEquivWasSetByUser = true;
        break;
      }
      case OptionEnum::QUANT_DSPLIT:
      {
        auto value = stringToQuantDSplitMode(optionarg);
        opts.writeQuantifiers().quantDynamicSplit = value;
        opts.writeQuantifiers().quantDynamicSplitWasSetByUser = true;
        break;
      }
      case OptionEnum::QUANT_FUN_WD:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().quantFunWellDefined = value;
        opts.writeQuantifiers().quantFunWellDefinedWasSetByUser = true;
        break;
      }
      case OptionEnum::QUANT_IND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().quantInduction = value;
        opts.writeQuantifiers().quantInductionWasSetByUser = true;
        break;
      }
      case OptionEnum::QUANT_REP_MODE:
      {
        auto value = stringToQuantRepMode(optionarg);
        opts.writeQuantifiers().quantRepMode = value;
        opts.writeQuantifiers().quantRepModeWasSetByUser = true;
        break;
      }
      case OptionEnum::QUIET:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().decreaseVerbosity(name, value);
        break;
      }
      case OptionEnum::RANDOM_FREQ:
      {
        auto value = handlers::handleOption<double>(name, optionarg);
        opts.handler().checkMinimum(name, value, static_cast<double>(0.0));
        opts.handler().checkMaximum(name, value, static_cast<double>(1.0));
        opts.writeProp().satRandomFreq = value;
        opts.writeProp().satRandomFreqWasSetByUser = true;
        break;
      }
      case OptionEnum::RE_ELIM:
      {
        auto value = stringToRegExpElimMode(optionarg);
        opts.writeStrings().regExpElim = value;
        opts.writeStrings().regExpElimWasSetByUser = true;
        break;
      }
      case OptionEnum::RE_INTER_MODE:
      {
        auto value = stringToRegExpInterMode(optionarg);
        opts.writeStrings().stringRegExpInterMode = value;
        opts.writeStrings().stringRegExpInterModeWasSetByUser = true;
        break;
      }
      case OptionEnum::REGISTER_QUANT_BODY_TERMS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().registerQuantBodyTerms = value;
        opts.writeQuantifiers().registerQuantBodyTermsWasSetByUser = true;
        break;
      }
      case OptionEnum::RELATIONAL_TRIGGERS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().relationalTriggers = value;
        opts.writeQuantifiers().relationalTriggersWasSetByUser = true;
        break;
      }
      case OptionEnum::RELEVANCE_FILTER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeTheory().relevanceFilter = value;
        opts.writeTheory().relevanceFilterWasSetByUser = true;
        break;
      }
      case OptionEnum::RELEVANT_TRIGGERS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().relevantTriggers = value;
        opts.writeQuantifiers().relevantTriggersWasSetByUser = true;
        break;
      }
      case OptionEnum::REPEAT_SIMP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().repeatSimp = value;
        opts.writeSmt().repeatSimpWasSetByUser = true;
        break;
      }
      case OptionEnum::REPLAY_EARLY_CLOSE_DEPTH:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().replayEarlyCloseDepths = value;
        opts.writeArith().replayEarlyCloseDepthsWasSetByUser = true;
        break;
      }
      case OptionEnum::REPLAY_LEMMA_REJECT_CUT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().lemmaRejectCutSize = value;
        opts.writeArith().lemmaRejectCutSizeWasSetByUser = true;
        break;
      }
      case OptionEnum::REPLAY_NUM_ERR_PENALTY:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().replayNumericFailurePenalty = value;
        opts.writeArith().replayNumericFailurePenaltyWasSetByUser = true;
        break;
      }
      case OptionEnum::REPLAY_REJECT_CUT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().replayRejectCutSize = value;
        opts.writeArith().replayRejectCutSizeWasSetByUser = true;
        break;
      }
      case OptionEnum::RESTART_INT_BASE:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeProp().satRestartFirst = value;
        opts.writeProp().satRestartFirstWasSetByUser = true;
        break;
      }
      case OptionEnum::RESTART_INT_INC:
      {
        auto value = handlers::handleOption<double>(name, optionarg);
        opts.handler().checkMinimum(name, value, static_cast<double>(0.0));
        opts.writeProp().satRestartInc = value;
        opts.writeProp().satRestartIncWasSetByUser = true;
        break;
      }
      case OptionEnum::RESTRICT_PIVOTS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().restrictedPivots = value;
        opts.writeArith().restrictedPivotsWasSetByUser = true;
        break;
      }
      case OptionEnum::REVERT_ARITH_MODELS_ON_UNSAT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().revertArithModels = value;
        opts.writeArith().revertArithModelsWasSetByUser = true;
        break;
      }
      case OptionEnum::RLIMIT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeBase().cumulativeResourceLimit = value;
        opts.writeBase().cumulativeResourceLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::RLIMIT_PER:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeBase().perCallResourceLimit = value;
        opts.writeBase().perCallResourceLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::RR_TURNS:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().rrTurns = value;
        opts.writeArith().rrTurnsWasSetByUser = true;
        break;
      }
      case OptionEnum::RWEIGHT:
      {
        auto value = handlers::handleOption<std::string>(name, optionarg);
        opts.handler().setResourceWeight(name, value);
        break;
      }
      case OptionEnum::SAT_RANDOM_SEED:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeProp().satRandomSeed = value;
        opts.writeProp().satRandomSeedWasSetByUser = true;
        break;
      }
      case OptionEnum::SE_SOLVE_INT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().trySolveIntStandardEffort = value;
        opts.writeArith().trySolveIntStandardEffortWasSetByUser = true;
        break;
      }
      case OptionEnum::SEED:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeDriver().seed = value;
        opts.writeDriver().seedWasSetByUser = true;
        break;
      }
      case OptionEnum::SEGV_SPIN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().segvSpin = value;
        opts.writeDriver().segvSpinWasSetByUser = true;
        break;
      }
      case OptionEnum::SEMANTIC_CHECKS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeParser().semanticChecks = value;
        opts.writeParser().semanticChecksWasSetByUser = true;
        break;
      }
      case OptionEnum::SEP_MIN_REFINE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSep().sepMinimalRefine = value;
        opts.writeSep().sepMinimalRefineWasSetByUser = true;
        break;
      }
      case OptionEnum::SEP_PRE_SKOLEM_EMP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSep().sepPreSkolemEmp = value;
        opts.writeSep().sepPreSkolemEmpWasSetByUser = true;
        break;
      }
      case OptionEnum::SEQ_ARRAY:
      {
        auto value = stringToSeqArrayMode(optionarg);
        opts.writeStrings().seqArray = value;
        opts.writeStrings().seqArrayWasSetByUser = true;
        break;
      }
      case OptionEnum::SETS_EXT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSets().setsExt = value;
        opts.writeSets().setsExtWasSetByUser = true;
        break;
      }
      case OptionEnum::SETS_INFER_AS_LEMMAS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSets().setsInferAsLemmas = value;
        opts.writeSets().setsInferAsLemmasWasSetByUser = true;
        break;
      }
      case OptionEnum::SETS_PROXY_LEMMAS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSets().setsProxyLemmas = value;
        opts.writeSets().setsProxyLemmasWasSetByUser = true;
        break;
      }
      case OptionEnum::SHOW_CONFIG:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().showConfiguration(name, value);
        opts.writeDriver().showConfiguration = value;
        opts.writeDriver().showConfigurationWasSetByUser = true;
        break;
      }
      case OptionEnum::SHOW_TRACE_TAGS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().showTraceTags(name, value);
        opts.writeDriver().showTraceTags = value;
        opts.writeDriver().showTraceTagsWasSetByUser = true;
        break;
      }
      case OptionEnum::SIMP_ITE_COMPRESS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().compressItes = value;
        opts.writeSmt().compressItesWasSetByUser = true;
        break;
      }
      case OptionEnum::SIMP_WITH_CARE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().simplifyWithCareEnabled = value;
        opts.writeSmt().simplifyWithCareEnabledWasSetByUser = true;
        break;
      }
      case OptionEnum::SIMPLEX_CHECK_PERIOD:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeArith().arithSimplexCheckPeriod = value;
        opts.writeArith().arithSimplexCheckPeriodWasSetByUser = true;
        break;
      }
      case OptionEnum::SIMPLIFICATION:
      {
        auto value = stringToSimplificationMode(optionarg);
        opts.writeSmt().simplificationMode = value;
        opts.writeSmt().simplificationModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SIMPLIFICATION_BCP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().simplificationBoolConstProp = value;
        opts.writeSmt().simplificationBoolConstPropWasSetByUser = true;
        break;
      }
      case OptionEnum::SOI_QE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().soiQuickExplain = value;
        opts.writeArith().soiQuickExplainWasSetByUser = true;
        break;
      }
      case OptionEnum::SOLVE_BV_AS_INT:
      {
        auto value = stringToSolveBVAsIntMode(optionarg);
        opts.writeSmt().solveBVAsInt = value;
        opts.writeSmt().solveBVAsIntWasSetByUser = true;
        break;
      }
      case OptionEnum::SOLVE_INT_AS_BV:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.handler().checkMaximum(name, value, static_cast<uint64_t>(4294967295));
        opts.writeSmt().solveIntAsBV = value;
        opts.writeSmt().solveIntAsBVWasSetByUser = true;
        break;
      }
      case OptionEnum::SOLVE_REAL_AS_INT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().solveRealAsInt = value;
        opts.writeSmt().solveRealAsIntWasSetByUser = true;
        break;
      }
      case OptionEnum::SORT_INFERENCE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().sortInference = value;
        opts.writeSmt().sortInferenceWasSetByUser = true;
        break;
      }
      case OptionEnum::STANDARD_EFFORT_VARIABLE_ORDER_PIVOTS:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeArith().arithStandardCheckVarOrderPivots = value;
        opts.writeArith().arithStandardCheckVarOrderPivotsWasSetByUser = true;
        break;
      }
      case OptionEnum::STATIC_LEARNING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().staticLearning = value;
        opts.writeSmt().staticLearningWasSetByUser = true;
        break;
      }
      case OptionEnum::STATS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().setStats(name, value);
        opts.writeBase().statistics = value;
        opts.writeBase().statisticsWasSetByUser = true;
        break;
      }
      case OptionEnum::STATS_ALL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().setStatsDetail(name, value);
        opts.writeBase().statisticsAll = value;
        opts.writeBase().statisticsAllWasSetByUser = true;
        break;
      }
      case OptionEnum::STATS_EVERY_QUERY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().setStatsDetail(name, value);
        opts.writeBase().statisticsEveryQuery = value;
        opts.writeBase().statisticsEveryQueryWasSetByUser = true;
        break;
      }
      case OptionEnum::STATS_INTERNAL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().setStatsDetail(name, value);
        opts.writeBase().statisticsInternal = value;
        opts.writeBase().statisticsInternalWasSetByUser = true;
        break;
      }
      case OptionEnum::STDIN_INPUT_PER_LINE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().stdinInputPerLine = value;
        opts.writeDriver().stdinInputPerLineWasSetByUser = true;
        break;
      }
      case OptionEnum::STRICT_PARSING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeParser().strictParsing = value;
        opts.writeParser().strictParsingWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_ALPHA_CARD:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.handler().checkMaximum(name, value, static_cast<uint64_t>(196608));
        opts.writeStrings().stringsAlphaCard = value;
        opts.writeStrings().stringsAlphaCardWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_CHECK_ENTAIL_LEN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringCheckEntailLen = value;
        opts.writeStrings().stringCheckEntailLenWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_CODE_ELIM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringsCodeElim = value;
        opts.writeStrings().stringsCodeElimWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_DEQ_EXT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringsDeqExt = value;
        opts.writeStrings().stringsDeqExtWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_EAGER_EVAL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringEagerEval = value;
        opts.writeStrings().stringEagerEvalWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_EAGER_LEN_RE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringsEagerLenEntRegexp = value;
        opts.writeStrings().stringsEagerLenEntRegexpWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_EAGER_REG:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringEagerReg = value;
        opts.writeStrings().stringEagerRegWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_EAGER_SOLVER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringEagerSolver = value;
        opts.writeStrings().stringEagerSolverWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_EXP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringExp = value;
        opts.writeStrings().stringExpWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_FF:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringFlatForms = value;
        opts.writeStrings().stringFlatFormsWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_FMF:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringFMF = value;
        opts.writeStrings().stringFMFWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_INFER_AS_LEMMAS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringInferAsLemmas = value;
        opts.writeStrings().stringInferAsLemmasWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_INFER_SYM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringInferSym = value;
        opts.writeStrings().stringInferSymWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_LAZY_PP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringLazyPreproc = value;
        opts.writeStrings().stringLazyPreprocWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_LEN_NORM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringLenNorm = value;
        opts.writeStrings().stringLenNormWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_MBR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringModelBasedReduction = value;
        opts.writeStrings().stringModelBasedReductionWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_MODEL_MAX_LEN:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeStrings().stringsModelMaxLength = value;
        opts.writeStrings().stringsModelMaxLengthWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_PROCESS_LOOP_MODE:
      {
        auto value = stringToProcessLoopMode(optionarg);
        opts.writeStrings().stringProcessLoopMode = value;
        opts.writeStrings().stringProcessLoopModeWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_RE_POSC_EAGER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringRegexpPosConcatEager = value;
        opts.writeStrings().stringRegexpPosConcatEagerWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_REGEXP_INCLUSION:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringRegexpInclusion = value;
        opts.writeStrings().stringRegexpInclusionWasSetByUser = true;
        break;
      }
      case OptionEnum::STRINGS_REXPLAIN_LEMMAS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeStrings().stringRExplainLemmas = value;
        opts.writeStrings().stringRExplainLemmasWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygus = value;
        opts.writeQuantifiers().sygusWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_ABORT_SIZE:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeDatatypes().sygusAbortSize = value;
        opts.writeDatatypes().sygusAbortSizeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_ADD_CONST_GRAMMAR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusAddConstGrammar = value;
        opts.writeQuantifiers().sygusAddConstGrammarWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_ARG_RELEVANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusArgRelevant = value;
        opts.writeQuantifiers().sygusArgRelevantWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_AUTO_UNFOLD:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusInvAutoUnfold = value;
        opts.writeQuantifiers().sygusInvAutoUnfoldWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_BOOL_ITE_RETURN_CONST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusBoolIteReturnConst = value;
        opts.writeQuantifiers().sygusBoolIteReturnConstWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_CORE_CONNECTIVE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusCoreConnective = value;
        opts.writeQuantifiers().sygusCoreConnectiveWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_CREPAIR_ABORT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusConstRepairAbort = value;
        opts.writeQuantifiers().sygusConstRepairAbortWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_ENUM:
      {
        auto value = stringToSygusEnumMode(optionarg);
        opts.writeQuantifiers().sygusEnumMode = value;
        opts.writeQuantifiers().sygusEnumModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_ENUM_FAST_NUM_CONSTS:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeQuantifiers().sygusEnumFastNumConsts = value;
        opts.writeQuantifiers().sygusEnumFastNumConstsWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_ENUM_RANDOM_P:
      {
        auto value = handlers::handleOption<double>(name, optionarg);
        opts.handler().checkMinimum(name, value, static_cast<double>(0.0));
        opts.handler().checkMaximum(name, value, static_cast<double>(1.0));
        opts.writeQuantifiers().sygusEnumRandomP = value;
        opts.writeQuantifiers().sygusEnumRandomPWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_EVAL_UNFOLD:
      {
        auto value = stringToSygusEvalUnfoldMode(optionarg);
        opts.writeQuantifiers().sygusEvalUnfoldMode = value;
        opts.writeQuantifiers().sygusEvalUnfoldModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_EXPR_MINER_CHECK_TIMEOUT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeQuantifiers().sygusExprMinerCheckTimeout = value;
        opts.writeQuantifiers().sygusExprMinerCheckTimeoutWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_FAIR:
      {
        auto value = stringToSygusFairMode(optionarg);
        opts.writeDatatypes().sygusFair = value;
        opts.writeDatatypes().sygusFairWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_FAIR_MAX:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().sygusFairMax = value;
        opts.writeDatatypes().sygusFairMaxWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_FILTER_SOL:
      {
        auto value = stringToSygusFilterSolMode(optionarg);
        opts.writeQuantifiers().sygusFilterSolMode = value;
        opts.writeQuantifiers().sygusFilterSolModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_FILTER_SOL_REV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusFilterSolRevSubsume = value;
        opts.writeQuantifiers().sygusFilterSolRevSubsumeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_GRAMMAR_CONS:
      {
        auto value = stringToSygusGrammarConsMode(optionarg);
        opts.writeQuantifiers().sygusGrammarConsMode = value;
        opts.writeQuantifiers().sygusGrammarConsModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_GRAMMAR_NORM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusGrammarNorm = value;
        opts.writeQuantifiers().sygusGrammarNormWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_INFERENCE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusInference = value;
        opts.writeQuantifiers().sygusInferenceWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_INST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusInst = value;
        opts.writeQuantifiers().sygusInstWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_INST_MODE:
      {
        auto value = stringToSygusInstMode(optionarg);
        opts.writeQuantifiers().sygusInstMode = value;
        opts.writeQuantifiers().sygusInstModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_INST_SCOPE:
      {
        auto value = stringToSygusInstScope(optionarg);
        opts.writeQuantifiers().sygusInstScope = value;
        opts.writeQuantifiers().sygusInstScopeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_INST_TERM_SEL:
      {
        auto value = stringToSygusInstTermSelMode(optionarg);
        opts.writeQuantifiers().sygusInstTermSel = value;
        opts.writeQuantifiers().sygusInstTermSelWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_INV_TEMPL:
      {
        auto value = stringToSygusInvTemplMode(optionarg);
        opts.writeQuantifiers().sygusInvTemplMode = value;
        opts.writeQuantifiers().sygusInvTemplModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_INV_TEMPL_WHEN_SG:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusInvTemplWhenSyntax = value;
        opts.writeQuantifiers().sygusInvTemplWhenSyntaxWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_MIN_GRAMMAR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusMinGrammar = value;
        opts.writeQuantifiers().sygusMinGrammarWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_OUT:
      {
        auto value = stringToSygusSolutionOutMode(optionarg);
        opts.writeQuantifiers().sygusOut = value;
        opts.writeQuantifiers().sygusOutWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_PBE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusUnifPbe = value;
        opts.writeQuantifiers().sygusUnifPbeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_PBE_MULTI_FAIR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusPbeMultiFair = value;
        opts.writeQuantifiers().sygusPbeMultiFairWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_PBE_MULTI_FAIR_DIFF:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().sygusPbeMultiFairDiff = value;
        opts.writeQuantifiers().sygusPbeMultiFairDiffWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_QE_PREPROC:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusQePreproc = value;
        opts.writeQuantifiers().sygusQePreprocWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_QUERY_GEN:
      {
        auto value = stringToSygusQueryGenMode(optionarg);
        opts.writeQuantifiers().sygusQueryGen = value;
        opts.writeQuantifiers().sygusQueryGenWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_QUERY_GEN_DUMP_FILES:
      {
        auto value = stringToSygusQueryDumpFilesMode(optionarg);
        opts.writeQuantifiers().sygusQueryGenDumpFiles = value;
        opts.writeQuantifiers().sygusQueryGenDumpFilesWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_QUERY_GEN_THRESH:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeQuantifiers().sygusQueryGenThresh = value;
        opts.writeQuantifiers().sygusQueryGenThreshWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_REC_FUN:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRecFun = value;
        opts.writeQuantifiers().sygusRecFunWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_REC_FUN_EVAL_LIMIT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeQuantifiers().sygusRecFunEvalLimit = value;
        opts.writeQuantifiers().sygusRecFunEvalLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_REPAIR_CONST:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRepairConst = value;
        opts.writeQuantifiers().sygusRepairConstWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_REPAIR_CONST_TIMEOUT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeQuantifiers().sygusRepairConstTimeout = value;
        opts.writeQuantifiers().sygusRepairConstTimeoutWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_REWRITER:
      {
        auto value = stringToSygusRewriterMode(optionarg);
        opts.writeDatatypes().sygusRewriter = value;
        opts.writeDatatypes().sygusRewriterWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynth = value;
        opts.writeQuantifiers().sygusRewSynthWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_ACCEL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthAccel = value;
        opts.writeQuantifiers().sygusRewSynthAccelWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_CHECK:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthCheck = value;
        opts.writeQuantifiers().sygusRewSynthCheckWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_CONG:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthFilterCong = value;
        opts.writeQuantifiers().sygusRewSynthFilterCongWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_MATCH:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthFilterMatch = value;
        opts.writeQuantifiers().sygusRewSynthFilterMatchWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_NL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthFilterNonLinear = value;
        opts.writeQuantifiers().sygusRewSynthFilterNonLinearWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_FILTER_ORDER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthFilterOrder = value;
        opts.writeQuantifiers().sygusRewSynthFilterOrderWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_INPUT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthInput = value;
        opts.writeQuantifiers().sygusRewSynthInputWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_INPUT_NVARS:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthInputNVars = value;
        opts.writeQuantifiers().sygusRewSynthInputNVarsWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_INPUT_USE_BOOL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthInputUseBool = value;
        opts.writeQuantifiers().sygusRewSynthInputUseBoolWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_SYNTH_REC:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewSynthRec = value;
        opts.writeQuantifiers().sygusRewSynthRecWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_RR_VERIFY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusRewVerify = value;
        opts.writeQuantifiers().sygusRewVerifyWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SAMPLE_FP_UNIFORM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusSampleFpUniform = value;
        opts.writeQuantifiers().sygusSampleFpUniformWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SAMPLE_GRAMMAR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusSampleGrammar = value;
        opts.writeQuantifiers().sygusSampleGrammarWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SAMPLES:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().sygusSamples = value;
        opts.writeQuantifiers().sygusSamplesWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SI:
      {
        auto value = stringToCegqiSingleInvMode(optionarg);
        opts.writeQuantifiers().cegqiSingleInvMode = value;
        opts.writeQuantifiers().cegqiSingleInvModeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SI_ABORT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().cegqiSingleInvAbort = value;
        opts.writeQuantifiers().cegqiSingleInvAbortWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SI_RCONS:
      {
        auto value = stringToCegqiSingleInvRconsMode(optionarg);
        opts.writeQuantifiers().cegqiSingleInvReconstruct = value;
        opts.writeQuantifiers().cegqiSingleInvReconstructWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SI_RCONS_LIMIT:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().cegqiSingleInvReconstructLimit = value;
        opts.writeQuantifiers().cegqiSingleInvReconstructLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SIMPLE_SYM_BREAK:
      {
        auto value = stringToSygusSimpleSymBreakMode(optionarg);
        opts.writeDatatypes().sygusSimpleSymBreak = value;
        opts.writeDatatypes().sygusSimpleSymBreakWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_STREAM:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusStream = value;
        opts.writeQuantifiers().sygusStreamWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SYM_BREAK_LAZY:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().sygusSymBreakLazy = value;
        opts.writeDatatypes().sygusSymBreakLazyWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SYM_BREAK_PBE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().sygusSymBreakPbe = value;
        opts.writeDatatypes().sygusSymBreakPbeWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_SYM_BREAK_RLV:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDatatypes().sygusSymBreakRlv = value;
        opts.writeDatatypes().sygusSymBreakRlvWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_UNIF_COND_INDEPENDENT_NO_REPEAT_SOL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusUnifCondIndNoRepeatSol = value;
        opts.writeQuantifiers().sygusUnifCondIndNoRepeatSolWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_UNIF_PI:
      {
        auto value = stringToSygusUnifPiMode(optionarg);
        opts.writeQuantifiers().sygusUnifPi = value;
        opts.writeQuantifiers().sygusUnifPiWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_UNIF_SHUFFLE_COND:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().sygusUnifShuffleCond = value;
        opts.writeQuantifiers().sygusUnifShuffleCondWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_VERIFY_INST_MAX_ROUNDS:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeQuantifiers().sygusVerifyInstMaxRounds = value;
        opts.writeQuantifiers().sygusVerifyInstMaxRoundsWasSetByUser = true;
        break;
      }
      case OptionEnum::SYGUS_VERIFY_TIMEOUT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeQuantifiers().sygusVerifyTimeout = value;
        opts.writeQuantifiers().sygusVerifyTimeoutWasSetByUser = true;
        break;
      }
      case OptionEnum::SYMMETRY_BREAKER:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeUf().ufSymmetryBreaker = value;
        opts.writeUf().ufSymmetryBreakerWasSetByUser = true;
        break;
      }
      case OptionEnum::TC_MODE:
      {
        auto value = stringToTcMode(optionarg);
        opts.writeTheory().tcMode = value;
        opts.writeTheory().tcModeWasSetByUser = true;
        break;
      }
      case OptionEnum::TERM_DB_CD:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().termDbCd = value;
        opts.writeQuantifiers().termDbCdWasSetByUser = true;
        break;
      }
      case OptionEnum::TERM_DB_MODE:
      {
        auto value = stringToTermDbMode(optionarg);
        opts.writeQuantifiers().termDbMode = value;
        opts.writeQuantifiers().termDbModeWasSetByUser = true;
        break;
      }
      case OptionEnum::THEORYOF_MODE:
      {
        auto value = stringToTheoryOfMode(optionarg);
        opts.writeTheory().theoryOfMode = value;
        opts.writeTheory().theoryOfModeWasSetByUser = true;
        break;
      }
      case OptionEnum::TLIMIT:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeBase().cumulativeMillisecondLimit = value;
        opts.writeBase().cumulativeMillisecondLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::TLIMIT_PER:
      {
        auto value = handlers::handleOption<uint64_t>(name, optionarg);
        opts.writeBase().perCallMillisecondLimit = value;
        opts.writeBase().perCallMillisecondLimitWasSetByUser = true;
        break;
      }
      case OptionEnum::TRACE:
      {
        auto value = handlers::handleOption<std::string>(name, optionarg);
        opts.handler().enableTraceTag(name, value);
        break;
      }
      case OptionEnum::TRIGGER_ACTIVE_SEL:
      {
        auto value = stringToTriggerActiveSelMode(optionarg);
        opts.writeQuantifiers().triggerActiveSelMode = value;
        opts.writeQuantifiers().triggerActiveSelModeWasSetByUser = true;
        break;
      }
      case OptionEnum::TRIGGER_SEL:
      {
        auto value = stringToTriggerSelMode(optionarg);
        opts.writeQuantifiers().triggerSelMode = value;
        opts.writeQuantifiers().triggerSelModeWasSetByUser = true;
        break;
      }
      case OptionEnum::TYPE_CHECKING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeExpr().typeChecking = value;
        opts.writeExpr().typeCheckingWasSetByUser = true;
        break;
      }
      case OptionEnum::UF_HO_EXT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeUf().ufHoExt = value;
        opts.writeUf().ufHoExtWasSetByUser = true;
        break;
      }
      case OptionEnum::UF_LAZY_LL:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeUf().ufHoLazyLambdaLift = value;
        opts.writeUf().ufHoLazyLambdaLiftWasSetByUser = true;
        break;
      }
      case OptionEnum::UF_SS:
      {
        auto value = stringToUfssMode(optionarg);
        opts.writeUf().ufssMode = value;
        opts.writeUf().ufssModeWasSetByUser = true;
        break;
      }
      case OptionEnum::UF_SS_ABORT_CARD:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.writeUf().ufssAbortCardinality = value;
        opts.writeUf().ufssAbortCardinalityWasSetByUser = true;
        break;
      }
      case OptionEnum::UF_SS_FAIR:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeUf().ufssFairness = value;
        opts.writeUf().ufssFairnessWasSetByUser = true;
        break;
      }
      case OptionEnum::UF_SS_FAIR_MONOTONE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeUf().ufssFairnessMonotone = value;
        opts.writeUf().ufssFairnessMonotoneWasSetByUser = true;
        break;
      }
      case OptionEnum::UNATE_LEMMAS:
      {
        auto value = stringToArithUnateLemmaMode(optionarg);
        opts.writeArith().arithUnateLemmaMode = value;
        opts.writeArith().arithUnateLemmaModeWasSetByUser = true;
        break;
      }
      case OptionEnum::UNCONSTRAINED_SIMP:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeSmt().unconstrainedSimp = value;
        opts.writeSmt().unconstrainedSimpWasSetByUser = true;
        break;
      }
      case OptionEnum::UNSAT_CORES_MODE:
      {
        auto value = stringToUnsatCoresMode(optionarg);
        opts.writeSmt().unsatCoresMode = value;
        opts.writeSmt().unsatCoresModeWasSetByUser = true;
        break;
      }
      case OptionEnum::USE_APPROX:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().useApprox = value;
        opts.writeArith().useApproxWasSetByUser = true;
        break;
      }
      case OptionEnum::USE_FCSIMPLEX:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().useFC = value;
        opts.writeArith().useFCWasSetByUser = true;
        break;
      }
      case OptionEnum::USE_PORTFOLIO:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeDriver().usePortfolio = value;
        opts.writeDriver().usePortfolioWasSetByUser = true;
        break;
      }
      case OptionEnum::USE_SOI:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeArith().useSOI = value;
        opts.writeArith().useSOIWasSetByUser = true;
        break;
      }
      case OptionEnum::USER_PAT:
      {
        auto value = stringToUserPatMode(optionarg);
        opts.writeQuantifiers().userPatternsQuant = value;
        opts.writeQuantifiers().userPatternsQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::USER_POOL:
      {
        auto value = stringToUserPoolMode(optionarg);
        opts.writeQuantifiers().userPoolQuant = value;
        opts.writeQuantifiers().userPoolQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::VAR_ELIM_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().varElimQuant = value;
        opts.writeQuantifiers().varElimQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::VAR_INEQ_ELIM_QUANT:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeQuantifiers().varIneqElimQuant = value;
        opts.writeQuantifiers().varIneqElimQuantWasSetByUser = true;
        break;
      }
      case OptionEnum::VERBOSE:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().increaseVerbosity(name, value);
        break;
      }
      case OptionEnum::VERBOSITY:
      {
        auto value = handlers::handleOption<int64_t>(name, optionarg);
        opts.handler().setVerbosity(name, value);
        opts.writeBase().verbosity = value;
        opts.writeBase().verbosityWasSetByUser = true;
        break;
      }
      case OptionEnum::VERSION:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.handler().showVersion(name, value);
        opts.writeDriver().showVersion = value;
        opts.writeDriver().showVersionWasSetByUser = true;
        break;
      }
      case OptionEnum::WF_CHECKING:
      {
        auto value = handlers::handleOption<bool>(name, optionarg);
        opts.writeExpr().wellFormedChecking = value;
        opts.writeExpr().wellFormedCheckingWasSetByUser = true;
        break;
      }
      case OptionEnum::WRITE_PARTITIONS_TO:
      {
        auto value = handlers::handleOption<ManagedOut>(name, optionarg);
        opts.writeParallel().partitionsOut = value;
        opts.writeParallel().partitionsOutWasSetByUser = true;
        break;
      }
    }
    // clang-format on
  }

#if defined(CVC5_MUZZLED) || defined(CVC5_COMPETITION_MODE)
#define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */
#define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC5_MUZZLED || CVC5_COMPETITION_MODE */

OptionInfo getInfo(const Options& opts, const std::string& name)
{
  // clang-format off
  auto it = NAME_TO_ENUM.find(name);
  if (it == NAME_TO_ENUM.end()) {
    throw OptionException("Unrecognized option key or setting: " + name);
  }
  switch (it->second) {
    case OptionEnum::ABSTRACT_VALUES:
      return OptionInfo{"abstract-values", {}, opts.smt.abstractValuesWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.abstractValues}};
    case OptionEnum::ACKERMANN:
      return OptionInfo{"ackermann", {}, opts.smt.ackermannWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.ackermann}};
    case OptionEnum::APPEND_LEARNED_LITERALS_TO_CUBES:
      return OptionInfo{"append-learned-literals-to-cubes", {}, opts.parallel.appendLearnedLiteralsToCubesWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.parallel.appendLearnedLiteralsToCubes}};
    case OptionEnum::APPROX_BRANCH_DEPTH:
      return OptionInfo{"approx-branch-depth", {}, opts.arith.maxApproxDepthWasSetByUser, OptionInfo::NumberInfo<int64_t>{200, opts.arith.maxApproxDepth, {}, {}}};
    case OptionEnum::ARITH_BRAB:
      return OptionInfo{"arith-brab", {}, opts.arith.brabTestWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.brabTest}};
    case OptionEnum::ARITH_EQ_SOLVER:
      return OptionInfo{"arith-eq-solver", {}, opts.arith.arithEqSolverWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.arithEqSolver}};
    case OptionEnum::ARITH_NO_PARTIAL_FUN:
      return OptionInfo{"arith-no-partial-fun", {}, opts.arith.arithNoPartialFunWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.arithNoPartialFun}};
    case OptionEnum::ARITH_PROP:
      return OptionInfo{"arith-prop", {}, opts.arith.arithPropagationModeWasSetByUser, OptionInfo::ModeInfo{"both", opts.arith.arithPropagationMode, { "bi", "both", "none", "unate" }}};
    case OptionEnum::ARITH_PROP_CLAUSES:
      return OptionInfo{"arith-prop-clauses", {}, opts.arith.arithPropAsLemmaLengthWasSetByUser, OptionInfo::NumberInfo<uint64_t>{8, opts.arith.arithPropAsLemmaLength, {}, {}}};
    case OptionEnum::ARITH_REWRITE_EQUALITIES:
      return OptionInfo{"arith-rewrite-equalities", {}, opts.arith.arithRewriteEqWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.arithRewriteEq}};
    case OptionEnum::ARITH_STATIC_LEARNING:
      return OptionInfo{"arith-static-learning", {}, opts.arith.arithStaticLearningWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.arithStaticLearning}};
    case OptionEnum::ARRAYS_EAGER_INDEX:
      return OptionInfo{"arrays-eager-index", {}, opts.arrays.arraysEagerIndexSplittingWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arrays.arraysEagerIndexSplitting}};
    case OptionEnum::ARRAYS_EAGER_LEMMAS:
      return OptionInfo{"arrays-eager-lemmas", {}, opts.arrays.arraysEagerLemmasWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arrays.arraysEagerLemmas}};
    case OptionEnum::ARRAYS_EXP:
      return OptionInfo{"arrays-exp", {}, opts.arrays.arraysExpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arrays.arraysExp}};
    case OptionEnum::ARRAYS_OPTIMIZE_LINEAR:
      return OptionInfo{"arrays-optimize-linear", {}, opts.arrays.arraysOptimizeLinearWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arrays.arraysOptimizeLinear}};
    case OptionEnum::ARRAYS_PROP:
      return OptionInfo{"arrays-prop", {}, opts.arrays.arraysPropagateWasSetByUser, OptionInfo::NumberInfo<int64_t>{2, opts.arrays.arraysPropagate, {}, {}}};
    case OptionEnum::ARRAYS_REDUCE_SHARING:
      return OptionInfo{"arrays-reduce-sharing", {}, opts.arrays.arraysReduceSharingWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arrays.arraysReduceSharing}};
    case OptionEnum::ARRAYS_WEAK_EQUIV:
      return OptionInfo{"arrays-weak-equiv", {}, opts.arrays.arraysWeakEquivalenceWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arrays.arraysWeakEquivalence}};
    case OptionEnum::ASSIGN_FUNCTION_VALUES:
      return OptionInfo{"assign-function-values", {}, opts.theory.assignFunctionValuesWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.theory.assignFunctionValues}};
    case OptionEnum::BITBLAST:
      return OptionInfo{"bitblast", {}, opts.bv.bitblastModeWasSetByUser, OptionInfo::ModeInfo{"lazy", opts.bv.bitblastMode, { "eager", "lazy" }}};
    case OptionEnum::BITWISE_EQ:
      return OptionInfo{"bitwise-eq", {}, opts.bv.bitwiseEqWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.bv.bitwiseEq}};
    case OptionEnum::BOOL_TO_BV:
      return OptionInfo{"bool-to-bv", {}, opts.bv.boolToBitvectorWasSetByUser, OptionInfo::ModeInfo{"off", opts.bv.boolToBitvector, { "all", "ite", "off" }}};
    case OptionEnum::BV_ASSERT_INPUT:
      return OptionInfo{"bv-assert-input", {}, opts.bv.bvAssertInputWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.bv.bvAssertInput}};
    case OptionEnum::BV_EAGER_EVAL:
      return OptionInfo{"bv-eager-eval", {}, opts.bv.bvEagerEvalWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.bv.bvEagerEval}};
    case OptionEnum::BV_GAUSS_ELIM:
      return OptionInfo{"bv-gauss-elim", {}, opts.bv.bvGaussElimWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.bv.bvGaussElim}};
    case OptionEnum::BV_INTRO_POW2:
      return OptionInfo{"bv-intro-pow2", {}, opts.bv.bvIntroducePow2WasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.bv.bvIntroducePow2}};
    case OptionEnum::BV_PRINT_CONSTS_AS_INDEXED_SYMBOLS:
      return OptionInfo{"bv-print-consts-as-indexed-symbols", {}, opts.printer.bvPrintConstsAsIndexedSymbolsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.printer.bvPrintConstsAsIndexedSymbols}};
    case OptionEnum::BV_PROPAGATE:
      return OptionInfo{"bv-propagate", {}, opts.bv.bitvectorPropagateWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.bv.bitvectorPropagate}};
    case OptionEnum::BV_RW_EXTEND_EQ:
      return OptionInfo{"bv-rw-extend-eq", {}, opts.bv.rwExtendEqWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.bv.rwExtendEq}};
    case OptionEnum::BV_SAT_SOLVER:
      return OptionInfo{"bv-sat-solver", {}, opts.bv.bvSatSolverWasSetByUser, OptionInfo::ModeInfo{"cadical", opts.bv.bvSatSolver, { "cadical", "cryptominisat", "kissat", "minisat" }}};
    case OptionEnum::BV_SOLVER:
      return OptionInfo{"bv-solver", {}, opts.bv.bvSolverWasSetByUser, OptionInfo::ModeInfo{"bitblast", opts.bv.bvSolver, { "bitblast", "bitblast-internal" }}};
    case OptionEnum::BV_TO_BOOL:
      return OptionInfo{"bv-to-bool", {}, opts.bv.bitvectorToBoolWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.bv.bitvectorToBool}};
    case OptionEnum::BV_TO_INT_USE_POW2:
      return OptionInfo{"bv-to-int-use-pow2", {}, opts.smt.bvToIntUsePow2WasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.bvToIntUsePow2}};
    case OptionEnum::BVAND_INTEGER_GRANULARITY:
      return OptionInfo{"bvand-integer-granularity", {}, opts.smt.BVAndIntegerGranularityWasSetByUser, OptionInfo::NumberInfo<uint64_t>{1, opts.smt.BVAndIntegerGranularity, {}, 8}};
    case OptionEnum::CBQI:
      return OptionInfo{"cbqi", {}, opts.quantifiers.conflictBasedInstWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.conflictBasedInst}};
    case OptionEnum::CBQI_ALL_CONFLICT:
      return OptionInfo{"cbqi-all-conflict", {}, opts.quantifiers.cbqiAllConflictWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cbqiAllConflict}};
    case OptionEnum::CBQI_EAGER_CHECK_RD:
      return OptionInfo{"cbqi-eager-check-rd", {}, opts.quantifiers.cbqiEagerCheckRdWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cbqiEagerCheckRd}};
    case OptionEnum::CBQI_EAGER_TEST:
      return OptionInfo{"cbqi-eager-test", {}, opts.quantifiers.cbqiEagerTestWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cbqiEagerTest}};
    case OptionEnum::CBQI_MODE:
      return OptionInfo{"cbqi-mode", {}, opts.quantifiers.cbqiModeWasSetByUser, OptionInfo::ModeInfo{"prop-eq", opts.quantifiers.cbqiMode, { "conflict", "prop-eq" }}};
    case OptionEnum::CBQI_SKIP_RD:
      return OptionInfo{"cbqi-skip-rd", {}, opts.quantifiers.cbqiSkipRdWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cbqiSkipRd}};
    case OptionEnum::CBQI_TCONSTRAINT:
      return OptionInfo{"cbqi-tconstraint", {}, opts.quantifiers.cbqiTConstraintWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cbqiTConstraint}};
    case OptionEnum::CBQI_VO_EXP:
      return OptionInfo{"cbqi-vo-exp", {}, opts.quantifiers.cbqiVoExpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cbqiVoExp}};
    case OptionEnum::CDT_BISIMILAR:
      return OptionInfo{"cdt-bisimilar", {}, opts.datatypes.cdtBisimilarWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.cdtBisimilar}};
    case OptionEnum::CEGIS_SAMPLE:
      return OptionInfo{"cegis-sample", {}, opts.quantifiers.cegisSampleWasSetByUser, OptionInfo::ModeInfo{"none", opts.quantifiers.cegisSample, { "none", "trust", "use" }}};
    case OptionEnum::CEGQI:
      return OptionInfo{"cegqi", {}, opts.quantifiers.cegqiWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqi}};
    case OptionEnum::CEGQI_ALL:
      return OptionInfo{"cegqi-all", {}, opts.quantifiers.cegqiAllWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiAll}};
    case OptionEnum::CEGQI_BV:
      return OptionInfo{"cegqi-bv", {}, opts.quantifiers.cegqiBvWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cegqiBv}};
    case OptionEnum::CEGQI_BV_CONCAT_INV:
      return OptionInfo{"cegqi-bv-concat-inv", {}, opts.quantifiers.cegqiBvConcInvWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cegqiBvConcInv}};
    case OptionEnum::CEGQI_BV_INEQ:
      return OptionInfo{"cegqi-bv-ineq", {}, opts.quantifiers.cegqiBvIneqModeWasSetByUser, OptionInfo::ModeInfo{"eq-boundary", opts.quantifiers.cegqiBvIneqMode, { "eq-boundary", "eq-slack", "keep" }}};
    case OptionEnum::CEGQI_BV_INTERLEAVE_VALUE:
      return OptionInfo{"cegqi-bv-interleave-value", {}, opts.quantifiers.cegqiBvInterleaveValueWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiBvInterleaveValue}};
    case OptionEnum::CEGQI_BV_LINEAR:
      return OptionInfo{"cegqi-bv-linear", {}, opts.quantifiers.cegqiBvLinearizeWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cegqiBvLinearize}};
    case OptionEnum::CEGQI_BV_RM_EXTRACT:
      return OptionInfo{"cegqi-bv-rm-extract", {}, opts.quantifiers.cegqiBvRmExtractWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cegqiBvRmExtract}};
    case OptionEnum::CEGQI_BV_SOLVE_NL:
      return OptionInfo{"cegqi-bv-solve-nl", {}, opts.quantifiers.cegqiBvSolveNlWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiBvSolveNl}};
    case OptionEnum::CEGQI_FULL:
      return OptionInfo{"cegqi-full", {}, opts.quantifiers.cegqiFullEffortWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiFullEffort}};
    case OptionEnum::CEGQI_INF_INT:
      return OptionInfo{"cegqi-inf-int", {}, opts.quantifiers.cegqiUseInfIntWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiUseInfInt}};
    case OptionEnum::CEGQI_INF_REAL:
      return OptionInfo{"cegqi-inf-real", {}, opts.quantifiers.cegqiUseInfRealWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiUseInfReal}};
    case OptionEnum::CEGQI_INNERMOST:
      return OptionInfo{"cegqi-innermost", {}, opts.quantifiers.cegqiInnermostWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cegqiInnermost}};
    case OptionEnum::CEGQI_MIDPOINT:
      return OptionInfo{"cegqi-midpoint", {}, opts.quantifiers.cegqiMidpointWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiMidpoint}};
    case OptionEnum::CEGQI_MIN_BOUNDS:
      return OptionInfo{"cegqi-min-bounds", {}, opts.quantifiers.cegqiMinBoundsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiMinBounds}};
    case OptionEnum::CEGQI_MULTI_INST:
      return OptionInfo{"cegqi-multi-inst", {}, opts.quantifiers.cegqiMultiInstWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiMultiInst}};
    case OptionEnum::CEGQI_NESTED_QE:
      return OptionInfo{"cegqi-nested-qe", {}, opts.quantifiers.cegqiNestedQEWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiNestedQE}};
    case OptionEnum::CEGQI_NOPT:
      return OptionInfo{"cegqi-nopt", {}, opts.quantifiers.cegqiNoptWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.cegqiNopt}};
    case OptionEnum::CEGQI_ROUND_UP_LIA:
      return OptionInfo{"cegqi-round-up-lia", {}, opts.quantifiers.cegqiRoundUpLowerLiaWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiRoundUpLowerLia}};
    case OptionEnum::CHECK_ABDUCTS:
      return OptionInfo{"check-abducts", {}, opts.smt.checkAbductsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.checkAbducts}};
    case OptionEnum::CHECK_INTERPOLANTS:
      return OptionInfo{"check-interpolants", {}, opts.smt.checkInterpolantsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.checkInterpolants}};
    case OptionEnum::CHECK_MODELS:
      return OptionInfo{"check-models", {}, opts.smt.checkModelsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.checkModels}};
    case OptionEnum::CHECK_PROOF_STEPS:
      return OptionInfo{"check-proof-steps", {}, opts.proof.checkProofStepsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.checkProofSteps}};
    case OptionEnum::CHECK_PROOFS:
      return OptionInfo{"check-proofs", {}, opts.smt.checkProofsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.checkProofs}};
    case OptionEnum::CHECK_SYNTH_SOL:
      return OptionInfo{"check-synth-sol", {}, opts.smt.checkSynthSolWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.checkSynthSol}};
    case OptionEnum::CHECK_UNSAT_CORES:
      return OptionInfo{"check-unsat-cores", {}, opts.smt.checkUnsatCoresWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.checkUnsatCores}};
    case OptionEnum::CHECKS_BEFORE_PARTITION:
      return OptionInfo{"checks-before-partition", {}, opts.parallel.checksBeforePartitioningWasSetByUser, OptionInfo::NumberInfo<uint64_t>{1, opts.parallel.checksBeforePartitioning, {}, {}}};
    case OptionEnum::CHECKS_BETWEEN_PARTITIONS:
      return OptionInfo{"checks-between-partitions", {}, opts.parallel.checksBetweenPartitionsWasSetByUser, OptionInfo::NumberInfo<uint64_t>{1, opts.parallel.checksBetweenPartitions, {}, {}}};
    case OptionEnum::COLLECT_PIVOT_STATS:
      return OptionInfo{"collect-pivot-stats", {}, opts.arith.collectPivotsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.collectPivots}};
    case OptionEnum::COMPUTE_PARTITIONS:
      return OptionInfo{"compute-partitions", {}, opts.parallel.computePartitionsWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.parallel.computePartitions, {}, {}}};
    case OptionEnum::COND_VAR_SPLIT_QUANT:
      return OptionInfo{"cond-var-split-quant", {}, opts.quantifiers.condVarSplitQuantWasSetByUser, OptionInfo::ModeInfo{"on", opts.quantifiers.condVarSplitQuant, { "agg", "off", "on" }}};
    case OptionEnum::CONDENSE_FUNCTION_VALUES:
      return OptionInfo{"condense-function-values", {}, opts.theory.condenseFunctionValuesWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.theory.condenseFunctionValues}};
    case OptionEnum::CONJECTURE_GEN:
      return OptionInfo{"conjecture-gen", {}, opts.quantifiers.conjectureGenWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.conjectureGen}};
    case OptionEnum::CONJECTURE_GEN_GT_ENUM:
      return OptionInfo{"conjecture-gen-gt-enum", {}, opts.quantifiers.conjectureGenGtEnumWasSetByUser, OptionInfo::NumberInfo<int64_t>{50, opts.quantifiers.conjectureGenGtEnum, {}, {}}};
    case OptionEnum::CONJECTURE_GEN_MAX_DEPTH:
      return OptionInfo{"conjecture-gen-max-depth", {}, opts.quantifiers.conjectureGenMaxDepthWasSetByUser, OptionInfo::NumberInfo<int64_t>{3, opts.quantifiers.conjectureGenMaxDepth, {}, {}}};
    case OptionEnum::CONJECTURE_GEN_PER_ROUND:
      return OptionInfo{"conjecture-gen-per-round", {}, opts.quantifiers.conjectureGenPerRoundWasSetByUser, OptionInfo::NumberInfo<int64_t>{1, opts.quantifiers.conjectureGenPerRound, {}, {}}};
    case OptionEnum::CONS_EXP_TRIGGERS:
      return OptionInfo{"cons-exp-triggers", {}, opts.quantifiers.consExpandTriggersWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.consExpandTriggers}};
    case OptionEnum::COPYRIGHT:
      return OptionInfo{"copyright", {}, opts.driver.showCopyrightWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.showCopyright}};
    case OptionEnum::CUT_ALL_BOUNDED:
      return OptionInfo{"cut-all-bounded", {}, opts.arith.doCutAllBoundedWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.doCutAllBounded}};
    case OptionEnum::DAG_THRESH:
      return OptionInfo{"dag-thresh", {}, opts.printer.dagThreshWasSetByUser, OptionInfo::NumberInfo<int64_t>{1, opts.printer.dagThresh, 0, {}}};
    case OptionEnum::DEBUG_CHECK_MODELS:
      return OptionInfo{"debug-check-models", {}, opts.smt.debugCheckModelsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.debugCheckModels}};
    case OptionEnum::DECISION:
      return OptionInfo{"decision", {"decision-mode"}, opts.decision.decisionModeWasSetByUser, OptionInfo::ModeInfo{"internal", opts.decision.decisionMode, { "internal", "justification", "stoponly" }}};
    case OptionEnum::DEEP_RESTART:
      return OptionInfo{"deep-restart", {}, opts.smt.deepRestartModeWasSetByUser, OptionInfo::ModeInfo{"none", opts.smt.deepRestartMode, { "all", "input", "input-and-prop", "input-and-solvable", "none" }}};
    case OptionEnum::DEEP_RESTART_FACTOR:
      return OptionInfo{"deep-restart-factor", {}, opts.smt.deepRestartFactorWasSetByUser, OptionInfo::NumberInfo<double>{3.0, opts.smt.deepRestartFactor, 0.0, 1000.0}};
    case OptionEnum::DIFFICULTY_MODE:
      return OptionInfo{"difficulty-mode", {}, opts.smt.difficultyModeWasSetByUser, OptionInfo::ModeInfo{"lemma-literal-all", opts.smt.difficultyMode, { "lemma-literal", "lemma-literal-all", "model-check" }}};
    case OptionEnum::DIO_DECOMPS:
      return OptionInfo{"dio-decomps", {}, opts.arith.exportDioDecompositionsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.exportDioDecompositions}};
    case OptionEnum::DIO_SOLVER:
      return OptionInfo{"dio-solver", {}, opts.arith.arithDioSolverWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.arithDioSolver}};
    case OptionEnum::DIO_TURNS:
      return OptionInfo{"dio-turns", {}, opts.arith.dioSolverTurnsWasSetByUser, OptionInfo::NumberInfo<int64_t>{10, opts.arith.dioSolverTurns, {}, {}}};
    case OptionEnum::DT_BINARY_SPLIT:
      return OptionInfo{"dt-binary-split", {}, opts.datatypes.dtBinarySplitWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.datatypes.dtBinarySplit}};
    case OptionEnum::DT_BLAST_SPLITS:
      return OptionInfo{"dt-blast-splits", {}, opts.datatypes.dtBlastSplitsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.datatypes.dtBlastSplits}};
    case OptionEnum::DT_CYCLIC:
      return OptionInfo{"dt-cyclic", {}, opts.datatypes.dtCyclicWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.dtCyclic}};
    case OptionEnum::DT_INFER_AS_LEMMAS:
      return OptionInfo{"dt-infer-as-lemmas", {}, opts.datatypes.dtInferAsLemmasWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.datatypes.dtInferAsLemmas}};
    case OptionEnum::DT_NESTED_REC:
      return OptionInfo{"dt-nested-rec", {}, opts.datatypes.dtNestedRecWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.datatypes.dtNestedRec}};
    case OptionEnum::DT_POLITE_OPTIMIZE:
      return OptionInfo{"dt-polite-optimize", {}, opts.datatypes.dtPoliteOptimizeWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.dtPoliteOptimize}};
    case OptionEnum::DT_SHARE_SEL:
      return OptionInfo{"dt-share-sel", {}, opts.datatypes.dtSharedSelectorsWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.dtSharedSelectors}};
    case OptionEnum::DT_STC_IND:
      return OptionInfo{"dt-stc-ind", {}, opts.quantifiers.dtStcInductionWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.dtStcInduction}};
    case OptionEnum::DT_VAR_EXP_QUANT:
      return OptionInfo{"dt-var-exp-quant", {}, opts.quantifiers.dtVarExpandQuantWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.dtVarExpandQuant}};
    case OptionEnum::DUMP_DIFFICULTY:
      return OptionInfo{"dump-difficulty", {}, opts.driver.dumpDifficultyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.dumpDifficulty}};
    case OptionEnum::DUMP_INSTANTIATIONS:
      return OptionInfo{"dump-instantiations", {}, opts.driver.dumpInstantiationsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.dumpInstantiations}};
    case OptionEnum::DUMP_INSTANTIATIONS_DEBUG:
      return OptionInfo{"dump-instantiations-debug", {}, opts.driver.dumpInstantiationsDebugWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.dumpInstantiationsDebug}};
    case OptionEnum::DUMP_MODELS:
      return OptionInfo{"dump-models", {}, opts.driver.dumpModelsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.dumpModels}};
    case OptionEnum::DUMP_PROOFS:
      return OptionInfo{"dump-proofs", {}, opts.driver.dumpProofsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.dumpProofs}};
    case OptionEnum::DUMP_UNSAT_CORES:
      return OptionInfo{"dump-unsat-cores", {}, opts.driver.dumpUnsatCoresWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.dumpUnsatCores}};
    case OptionEnum::E_MATCHING:
      return OptionInfo{"e-matching", {}, opts.quantifiers.eMatchingWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.eMatching}};
    case OptionEnum::EAGER_ARITH_BV_CONV:
      return OptionInfo{"eager-arith-bv-conv", {}, opts.uf.eagerArithBvConvWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.uf.eagerArithBvConv}};
    case OptionEnum::EARLY_EXIT:
      return OptionInfo{"early-exit", {}, opts.driver.earlyExitWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.driver.earlyExit}};
    case OptionEnum::EARLY_ITE_REMOVAL:
      return OptionInfo{"early-ite-removal", {}, opts.smt.earlyIteRemovalWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.earlyIteRemoval}};
    case OptionEnum::EE_MODE:
      return OptionInfo{"ee-mode", {}, opts.theory.eeModeWasSetByUser, OptionInfo::ModeInfo{"distributed", opts.theory.eeMode, { "central", "distributed" }}};
    case OptionEnum::ELIM_TAUT_QUANT:
      return OptionInfo{"elim-taut-quant", {}, opts.quantifiers.elimTautQuantWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.elimTautQuant}};
    case OptionEnum::ENUM_INST:
      return OptionInfo{"enum-inst", {}, opts.quantifiers.enumInstWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.enumInst}};
    case OptionEnum::ENUM_INST_INTERLEAVE:
      return OptionInfo{"enum-inst-interleave", {}, opts.quantifiers.enumInstInterleaveWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.enumInstInterleave}};
    case OptionEnum::ENUM_INST_LIMIT:
      return OptionInfo{"enum-inst-limit", {}, opts.quantifiers.enumInstLimitWasSetByUser, OptionInfo::NumberInfo<int64_t>{-1, opts.quantifiers.enumInstLimit, {}, {}}};
    case OptionEnum::ENUM_INST_RD:
      return OptionInfo{"enum-inst-rd", {}, opts.quantifiers.enumInstRdWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.enumInstRd}};
    case OptionEnum::ENUM_INST_STRATIFY:
      return OptionInfo{"enum-inst-stratify", {}, opts.quantifiers.enumInstStratifyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.enumInstStratify}};
    case OptionEnum::ENUM_INST_SUM:
      return OptionInfo{"enum-inst-sum", {}, opts.quantifiers.enumInstSumWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.enumInstSum}};
    case OptionEnum::ERR:
      return OptionInfo{"err", {"diagnostic-output-channel"}, opts.base.errWasSetByUser, OptionInfo::VoidInfo{}};
    case OptionEnum::ERROR_SELECTION_RULE:
      return OptionInfo{"error-selection-rule", {}, opts.arith.arithErrorSelectionRuleWasSetByUser, OptionInfo::ModeInfo{"min", opts.arith.arithErrorSelectionRule, { "max", "min", "sum", "varord" }}};
    case OptionEnum::EXPR_DEPTH:
      return OptionInfo{"expr-depth", {}, opts.printer.nodeDepthWasSetByUser, OptionInfo::NumberInfo<int64_t>{-1, opts.printer.nodeDepth, -1, {}}};
    case OptionEnum::EXT_REW_PREP:
      return OptionInfo{"ext-rew-prep", {}, opts.smt.extRewPrepWasSetByUser, OptionInfo::ModeInfo{"off", opts.smt.extRewPrep, { "agg", "off", "use" }}};
    case OptionEnum::EXT_REWRITE_QUANT:
      return OptionInfo{"ext-rewrite-quant", {}, opts.quantifiers.extRewriteQuantWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.extRewriteQuant}};
    case OptionEnum::FC_PENALTIES:
      return OptionInfo{"fc-penalties", {}, opts.arith.havePenaltiesWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.havePenalties}};
    case OptionEnum::FF_FIELD_POLYS:
      return OptionInfo{"ff-field-polys", {}, opts.ff.ffFieldPolysWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.ff.ffFieldPolys}};
    case OptionEnum::FF_TRACE_GB:
      return OptionInfo{"ff-trace-gb", {}, opts.ff.ffTraceGbWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.ff.ffTraceGb}};
    case OptionEnum::FILENAME:
      return OptionInfo{"filename", {}, opts.driver.filenameWasSetByUser, OptionInfo::ValueInfo<std::string>{"", opts.driver.filename}};
    case OptionEnum::FILESYSTEM_ACCESS:
      return OptionInfo{"filesystem-access", {}, opts.parser.filesystemAccessWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.parser.filesystemAccess}};
    case OptionEnum::FINITE_MODEL_FIND:
      return OptionInfo{"finite-model-find", {}, opts.quantifiers.finiteModelFindWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.finiteModelFind}};
    case OptionEnum::FLATTEN_HO_CHAINS:
      return OptionInfo{"flatten-ho-chains", {}, opts.printer.flattenHOChainsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.printer.flattenHOChains}};
    case OptionEnum::FLEX_PARSER:
      return OptionInfo{"flex-parser", {}, opts.parser.flexParserWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.parser.flexParser}};
    case OptionEnum::FMF_BOUND:
      return OptionInfo{"fmf-bound", {}, opts.quantifiers.fmfBoundWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.fmfBound}};
    case OptionEnum::FMF_BOUND_BLAST:
      return OptionInfo{"fmf-bound-blast", {}, opts.quantifiers.fmfBoundBlastWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.fmfBoundBlast}};
    case OptionEnum::FMF_BOUND_LAZY:
      return OptionInfo{"fmf-bound-lazy", {}, opts.quantifiers.fmfBoundLazyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.fmfBoundLazy}};
    case OptionEnum::FMF_FUN:
      return OptionInfo{"fmf-fun", {}, opts.quantifiers.fmfFunWellDefinedWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.fmfFunWellDefined}};
    case OptionEnum::FMF_FUN_RLV:
      return OptionInfo{"fmf-fun-rlv", {}, opts.quantifiers.fmfFunWellDefinedRelevantWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.fmfFunWellDefinedRelevant}};
    case OptionEnum::FMF_MBQI:
      return OptionInfo{"fmf-mbqi", {}, opts.quantifiers.fmfMbqiModeWasSetByUser, OptionInfo::ModeInfo{"fmc", opts.quantifiers.fmfMbqiMode, { "fmc", "none", "trust" }}};
    case OptionEnum::FMF_TYPE_COMPLETION_THRESH:
      return OptionInfo{"fmf-type-completion-thresh", {}, opts.quantifiers.fmfTypeCompletionThreshWasSetByUser, OptionInfo::NumberInfo<int64_t>{1000, opts.quantifiers.fmfTypeCompletionThresh, {}, {}}};
    case OptionEnum::FORCE_LOGIC:
      return OptionInfo{"force-logic", {}, opts.parser.forceLogicStringWasSetByUser, OptionInfo::ValueInfo<std::string>{"", opts.parser.forceLogicString}};
    case OptionEnum::FORCE_NO_LIMIT_CPU_WHILE_DUMP:
      return OptionInfo{"force-no-limit-cpu-while-dump", {}, opts.driver.forceNoLimitCpuWhileDumpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.forceNoLimitCpuWhileDump}};
    case OptionEnum::FOREIGN_THEORY_REWRITE:
      return OptionInfo{"foreign-theory-rewrite", {}, opts.smt.foreignTheoryRewriteWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.foreignTheoryRewrite}};
    case OptionEnum::FP_EXP:
      return OptionInfo{"fp-exp", {}, opts.fp.fpExpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.fp.fpExp}};
    case OptionEnum::FP_LAZY_WB:
      return OptionInfo{"fp-lazy-wb", {}, opts.fp.fpLazyWbWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.fp.fpLazyWb}};
    case OptionEnum::FULL_SATURATE_QUANT:
      return OptionInfo{"full-saturate-quant", {}, opts.quantifiers.fullSaturateQuantWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.fullSaturateQuant}};
    case OptionEnum::GLOBAL_DECLARATIONS:
      return OptionInfo{"global-declarations", {}, opts.parser.globalDeclarationsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.parser.globalDeclarations}};
    case OptionEnum::GLOBAL_NEGATE:
      return OptionInfo{"global-negate", {}, opts.quantifiers.globalNegateWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.globalNegate}};
    case OptionEnum::HELP:
      return OptionInfo{"help", {}, opts.driver.helpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.help}};
    case OptionEnum::HEURISTIC_PIVOTS:
      return OptionInfo{"heuristic-pivots", {}, opts.arith.arithHeuristicPivotsWasSetByUser, OptionInfo::NumberInfo<int64_t>{0, opts.arith.arithHeuristicPivots, {}, {}}};
    case OptionEnum::HO_ELIM:
      return OptionInfo{"ho-elim", {}, opts.quantifiers.hoElimWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.hoElim}};
    case OptionEnum::HO_ELIM_STORE_AX:
      return OptionInfo{"ho-elim-store-ax", {}, opts.quantifiers.hoElimStoreAxWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.hoElimStoreAx}};
    case OptionEnum::HO_MATCHING:
      return OptionInfo{"ho-matching", {}, opts.quantifiers.hoMatchingWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.hoMatching}};
    case OptionEnum::HO_MERGE_TERM_DB:
      return OptionInfo{"ho-merge-term-db", {}, opts.quantifiers.hoMergeTermDbWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.hoMergeTermDb}};
    case OptionEnum::IAND_MODE:
      return OptionInfo{"iand-mode", {}, opts.smt.iandModeWasSetByUser, OptionInfo::ModeInfo{"value", opts.smt.iandMode, { "bitwise", "sum", "value" }}};
    case OptionEnum::IEVAL:
      return OptionInfo{"ieval", {}, opts.quantifiers.ievalModeWasSetByUser, OptionInfo::ModeInfo{"off", opts.quantifiers.ievalMode, { "off", "use", "use-learn" }}};
    case OptionEnum::IN:
      return OptionInfo{"in", {}, opts.base.inWasSetByUser, OptionInfo::VoidInfo{}};
    case OptionEnum::INCREMENT_TRIGGERS:
      return OptionInfo{"increment-triggers", {}, opts.quantifiers.incrementTriggersWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.incrementTriggers}};
    case OptionEnum::INCREMENTAL:
      return OptionInfo{"incremental", {}, opts.base.incrementalSolvingWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.base.incrementalSolving}};
    case OptionEnum::INST_MAX_LEVEL:
      return OptionInfo{"inst-max-level", {}, opts.quantifiers.instMaxLevelWasSetByUser, OptionInfo::NumberInfo<int64_t>{-1, opts.quantifiers.instMaxLevel, {}, {}}};
    case OptionEnum::INST_MAX_ROUNDS:
      return OptionInfo{"inst-max-rounds", {}, opts.quantifiers.instMaxRoundsWasSetByUser, OptionInfo::NumberInfo<int64_t>{-1, opts.quantifiers.instMaxRounds, {}, {}}};
    case OptionEnum::INST_NO_ENTAIL:
      return OptionInfo{"inst-no-entail", {}, opts.quantifiers.instNoEntailWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.instNoEntail}};
    case OptionEnum::INST_WHEN:
      return OptionInfo{"inst-when", {}, opts.quantifiers.instWhenModeWasSetByUser, OptionInfo::ModeInfo{"full-last-call", opts.quantifiers.instWhenMode, { "full", "full-delay", "full-delay-last-call", "full-last-call", "last-call" }}};
    case OptionEnum::INST_WHEN_PHASE:
      return OptionInfo{"inst-when-phase", {}, opts.quantifiers.instWhenPhaseWasSetByUser, OptionInfo::NumberInfo<int64_t>{2, opts.quantifiers.instWhenPhase, {}, {}}};
    case OptionEnum::INT_WF_IND:
      return OptionInfo{"int-wf-ind", {}, opts.quantifiers.intWfInductionWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.intWfInduction}};
    case OptionEnum::INTERACTIVE:
      return OptionInfo{"interactive", {}, opts.driver.interactiveWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.interactive}};
    case OptionEnum::INTERPOLANTS_MODE:
      return OptionInfo{"interpolants-mode", {}, opts.smt.interpolantsModeWasSetByUser, OptionInfo::ModeInfo{"default", opts.smt.interpolantsMode, { "all", "assumptions", "conjecture", "default", "shared" }}};
    case OptionEnum::ITE_DTT_SPLIT_QUANT:
      return OptionInfo{"ite-dtt-split-quant", {}, opts.quantifiers.iteDtTesterSplitQuantWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.iteDtTesterSplitQuant}};
    case OptionEnum::ITE_LIFT_QUANT:
      return OptionInfo{"ite-lift-quant", {}, opts.quantifiers.iteLiftQuantWasSetByUser, OptionInfo::ModeInfo{"simple", opts.quantifiers.iteLiftQuant, { "all", "none", "simple" }}};
    case OptionEnum::ITE_SIMP:
      return OptionInfo{"ite-simp", {}, opts.smt.doITESimpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.doITESimp}};
    case OptionEnum::JH_RLV_ORDER:
      return OptionInfo{"jh-rlv-order", {}, opts.decision.jhRlvOrderWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.decision.jhRlvOrder}};
    case OptionEnum::JH_SKOLEM:
      return OptionInfo{"jh-skolem", {}, opts.decision.jhSkolemModeWasSetByUser, OptionInfo::ModeInfo{"first", opts.decision.jhSkolemMode, { "first", "last" }}};
    case OptionEnum::JH_SKOLEM_RLV:
      return OptionInfo{"jh-skolem-rlv", {}, opts.decision.jhSkolemRlvModeWasSetByUser, OptionInfo::ModeInfo{"assert", opts.decision.jhSkolemRlvMode, { "always", "assert" }}};
    case OptionEnum::LANG:
      return OptionInfo{"lang", {"input-language"}, opts.base.inputLanguageWasSetByUser, OptionInfo::VoidInfo{}};
    case OptionEnum::LEARNED_REWRITE:
      return OptionInfo{"learned-rewrite", {}, opts.smt.learnedRewriteWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.learnedRewrite}};
    case OptionEnum::LEMMAS_ON_REPLAY_FAILURE:
      return OptionInfo{"lemmas-on-replay-failure", {}, opts.arith.replayFailureLemmaWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.replayFailureLemma}};
    case OptionEnum::LFSC_EXPAND_TRUST:
      return OptionInfo{"lfsc-expand-trust", {}, opts.proof.lfscExpandTrustWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.lfscExpandTrust}};
    case OptionEnum::LFSC_FLATTEN:
      return OptionInfo{"lfsc-flatten", {}, opts.proof.lfscFlattenWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.lfscFlatten}};
    case OptionEnum::LITERAL_MATCHING:
      return OptionInfo{"literal-matching", {}, opts.quantifiers.literalMatchModeWasSetByUser, OptionInfo::ModeInfo{"use", opts.quantifiers.literalMatchMode, { "agg", "agg-predicate", "none", "use" }}};
    case OptionEnum::MACROS_QUANT:
      return OptionInfo{"macros-quant", {}, opts.quantifiers.macrosQuantWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.macrosQuant}};
    case OptionEnum::MACROS_QUANT_MODE:
      return OptionInfo{"macros-quant-mode", {}, opts.quantifiers.macrosQuantModeWasSetByUser, OptionInfo::ModeInfo{"ground-uf", opts.quantifiers.macrosQuantMode, { "all", "ground", "ground-uf" }}};
    case OptionEnum::MAXCUTSINCONTEXT:
      return OptionInfo{"maxCutsInContext", {}, opts.arith.maxCutsInContextWasSetByUser, OptionInfo::NumberInfo<uint64_t>{65535, opts.arith.maxCutsInContext, {}, {}}};
    case OptionEnum::MBQI:
      return OptionInfo{"mbqi", {}, opts.quantifiers.mbqiWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.mbqi}};
    case OptionEnum::MBQI_INTERLEAVE:
      return OptionInfo{"mbqi-interleave", {}, opts.quantifiers.mbqiInterleaveWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.mbqiInterleave}};
    case OptionEnum::MBQI_ONE_INST_PER_ROUND:
      return OptionInfo{"mbqi-one-inst-per-round", {}, opts.quantifiers.fmfOneInstPerRoundWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.fmfOneInstPerRound}};
    case OptionEnum::MINIMAL_UNSAT_CORES:
      return OptionInfo{"minimal-unsat-cores", {}, opts.smt.minimalUnsatCoresWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.minimalUnsatCores}};
    case OptionEnum::MINISAT_DUMP_DIMACS:
      return OptionInfo{"minisat-dump-dimacs", {}, opts.prop.minisatDumpDimacsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.prop.minisatDumpDimacs}};
    case OptionEnum::MINISAT_SIMPLIFICATION:
      return OptionInfo{"minisat-simplification", {}, opts.prop.minisatSimpModeWasSetByUser, OptionInfo::ModeInfo{"all", opts.prop.minisatSimpMode, { "all", "clause-elim", "none" }}};
    case OptionEnum::MINISCOPE_QUANT:
      return OptionInfo{"miniscope-quant", {}, opts.quantifiers.miniscopeQuantWasSetByUser, OptionInfo::ModeInfo{"conj-and-fv", opts.quantifiers.miniscopeQuant, { "agg", "conj", "conj-and-fv", "fv", "off" }}};
    case OptionEnum::MIPLIB_TRICK:
      return OptionInfo{"miplib-trick", {}, opts.arith.arithMLTrickWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.arithMLTrick}};
    case OptionEnum::MIPLIB_TRICK_SUBS:
      return OptionInfo{"miplib-trick-subs", {}, opts.arith.arithMLTrickSubstitutionsWasSetByUser, OptionInfo::NumberInfo<uint64_t>{1, opts.arith.arithMLTrickSubstitutions, {}, {}}};
    case OptionEnum::MODEL_CORES:
      return OptionInfo{"model-cores", {}, opts.smt.modelCoresModeWasSetByUser, OptionInfo::ModeInfo{"none", opts.smt.modelCoresMode, { "non-implied", "none", "simple" }}};
    case OptionEnum::MODEL_U_PRINT:
      return OptionInfo{"model-u-print", {}, opts.printer.modelUninterpPrintWasSetByUser, OptionInfo::ModeInfo{"none", opts.printer.modelUninterpPrint, { "decl-fun", "decl-sort-and-fun", "none" }}};
    case OptionEnum::MODEL_VAR_ELIM_UNEVAL:
      return OptionInfo{"model-var-elim-uneval", {}, opts.smt.modelVarElimUnevalWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.smt.modelVarElimUneval}};
    case OptionEnum::MULTI_TRIGGER_CACHE:
      return OptionInfo{"multi-trigger-cache", {}, opts.quantifiers.multiTriggerCacheWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.multiTriggerCache}};
    case OptionEnum::MULTI_TRIGGER_LINEAR:
      return OptionInfo{"multi-trigger-linear", {}, opts.quantifiers.multiTriggerLinearWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.multiTriggerLinear}};
    case OptionEnum::MULTI_TRIGGER_PRIORITY:
      return OptionInfo{"multi-trigger-priority", {}, opts.quantifiers.multiTriggerPriorityWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.multiTriggerPriority}};
    case OptionEnum::MULTI_TRIGGER_WHEN_SINGLE:
      return OptionInfo{"multi-trigger-when-single", {}, opts.quantifiers.multiTriggerWhenSingleWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.multiTriggerWhenSingle}};
    case OptionEnum::NEW_PROP:
      return OptionInfo{"new-prop", {}, opts.arith.newPropWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.newProp}};
    case OptionEnum::NL_COV:
      return OptionInfo{"nl-cov", {}, opts.arith.nlCovWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlCov}};
    case OptionEnum::NL_COV_FORCE:
      return OptionInfo{"nl-cov-force", {}, opts.arith.nlCovForceWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlCovForce}};
    case OptionEnum::NL_COV_LIFT:
      return OptionInfo{"nl-cov-lift", {}, opts.arith.nlCovLiftingWasSetByUser, OptionInfo::ModeInfo{"regular", opts.arith.nlCovLifting, { "lazard", "regular" }}};
    case OptionEnum::NL_COV_LINEAR_MODEL:
      return OptionInfo{"nl-cov-linear-model", {}, opts.arith.nlCovLinearModelWasSetByUser, OptionInfo::ModeInfo{"none", opts.arith.nlCovLinearModel, { "initial", "none", "persistent" }}};
    case OptionEnum::NL_COV_PROJ:
      return OptionInfo{"nl-cov-proj", {}, opts.arith.nlCovProjectionWasSetByUser, OptionInfo::ModeInfo{"mccallum", opts.arith.nlCovProjection, { "lazard", "lazard-mod", "mccallum" }}};
    case OptionEnum::NL_COV_PRUNE:
      return OptionInfo{"nl-cov-prune", {}, opts.arith.nlCovPruneWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlCovPrune}};
    case OptionEnum::NL_COV_VAR_ELIM:
      return OptionInfo{"nl-cov-var-elim", {}, opts.arith.nlCovVarElimWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.nlCovVarElim}};
    case OptionEnum::NL_EXT:
      return OptionInfo{"nl-ext", {}, opts.arith.nlExtWasSetByUser, OptionInfo::ModeInfo{"full", opts.arith.nlExt, { "full", "light", "none" }}};
    case OptionEnum::NL_EXT_ENT_CONF:
      return OptionInfo{"nl-ext-ent-conf", {}, opts.arith.nlExtEntailConflictsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlExtEntailConflicts}};
    case OptionEnum::NL_EXT_FACTOR:
      return OptionInfo{"nl-ext-factor", {}, opts.arith.nlExtFactorWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.nlExtFactor}};
    case OptionEnum::NL_EXT_INC_PREC:
      return OptionInfo{"nl-ext-inc-prec", {}, opts.arith.nlExtIncPrecisionWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.nlExtIncPrecision}};
    case OptionEnum::NL_EXT_PURIFY:
      return OptionInfo{"nl-ext-purify", {}, opts.arith.nlExtPurifyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlExtPurify}};
    case OptionEnum::NL_EXT_RBOUND:
      return OptionInfo{"nl-ext-rbound", {}, opts.arith.nlExtResBoundWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlExtResBound}};
    case OptionEnum::NL_EXT_REWRITE:
      return OptionInfo{"nl-ext-rewrite", {}, opts.arith.nlExtRewritesWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.nlExtRewrites}};
    case OptionEnum::NL_EXT_SPLIT_ZERO:
      return OptionInfo{"nl-ext-split-zero", {}, opts.arith.nlExtSplitZeroWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlExtSplitZero}};
    case OptionEnum::NL_EXT_TF_TAYLOR_DEG:
      return OptionInfo{"nl-ext-tf-taylor-deg", {}, opts.arith.nlExtTfTaylorDegreeWasSetByUser, OptionInfo::NumberInfo<int64_t>{4, opts.arith.nlExtTfTaylorDegree, {}, {}}};
    case OptionEnum::NL_EXT_TF_TPLANES:
      return OptionInfo{"nl-ext-tf-tplanes", {}, opts.arith.nlExtTfTangentPlanesWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.nlExtTfTangentPlanes}};
    case OptionEnum::NL_EXT_TPLANES:
      return OptionInfo{"nl-ext-tplanes", {}, opts.arith.nlExtTangentPlanesWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.nlExtTangentPlanes}};
    case OptionEnum::NL_EXT_TPLANES_INTERLEAVE:
      return OptionInfo{"nl-ext-tplanes-interleave", {}, opts.arith.nlExtTangentPlanesInterleaveWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlExtTangentPlanesInterleave}};
    case OptionEnum::NL_ICP:
      return OptionInfo{"nl-icp", {}, opts.arith.nlICPWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlICP}};
    case OptionEnum::NL_RLV:
      return OptionInfo{"nl-rlv", {}, opts.arith.nlRlvModeWasSetByUser, OptionInfo::ModeInfo{"none", opts.arith.nlRlvMode, { "always", "interleave", "none" }}};
    case OptionEnum::NL_RLV_ASSERT_BOUNDS:
      return OptionInfo{"nl-rlv-assert-bounds", {}, opts.arith.nlRlvAssertBoundsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.nlRlvAssertBounds}};
    case OptionEnum::ON_REPEAT_ITE_SIMP:
      return OptionInfo{"on-repeat-ite-simp", {}, opts.smt.doITESimpOnRepeatWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.doITESimpOnRepeat}};
    case OptionEnum::OPT_RES_RECONSTRUCTION_SIZE:
      return OptionInfo{"opt-res-reconstruction-size", {}, opts.proof.optResReconSizeWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.proof.optResReconSize}};
    case OptionEnum::ORACLES:
      return OptionInfo{"oracles", {}, opts.quantifiers.oraclesWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.oracles}};
    case OptionEnum::OUT:
      return OptionInfo{"out", {"regular-output-channel"}, opts.base.outWasSetByUser, OptionInfo::VoidInfo{}};
    case OptionEnum::OUTPUT:
      return OptionInfo{"output", {}, false, OptionInfo::VoidInfo{}};
    case OptionEnum::OUTPUT_LANG:
      return OptionInfo{"output-lang", {"output-language"}, opts.printer.outputLanguageWasSetByUser, OptionInfo::VoidInfo{}};
    case OptionEnum::PARSE_ONLY:
      return OptionInfo{"parse-only", {}, opts.base.parseOnlyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.base.parseOnly}};
    case OptionEnum::PARTIAL_TRIGGERS:
      return OptionInfo{"partial-triggers", {}, opts.quantifiers.partialTriggersWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.partialTriggers}};
    case OptionEnum::PARTITION_CHECK:
      return OptionInfo{"partition-check", {"check"}, opts.parallel.partitionCheckWasSetByUser, OptionInfo::ModeInfo{"standard", opts.parallel.partitionCheck, { "full", "standard" }}};
    case OptionEnum::PARTITION_CONFLICT_SIZE:
      return OptionInfo{"partition-conflict-size", {}, opts.parallel.partitionConflictSizeWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.parallel.partitionConflictSize, {}, {}}};
    case OptionEnum::PARTITION_STRATEGY:
      return OptionInfo{"partition-strategy", {"partition"}, opts.parallel.partitionStrategyWasSetByUser, OptionInfo::ModeInfo{"revised", opts.parallel.partitionStrategy, { "decision-trail", "heap-trail", "revised", "strict-cube" }}};
    case OptionEnum::PB_REWRITES:
      return OptionInfo{"pb-rewrites", {}, opts.arith.pbRewritesWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.pbRewrites}};
    case OptionEnum::PIVOT_THRESHOLD:
      return OptionInfo{"pivot-threshold", {}, opts.arith.arithPivotThresholdWasSetByUser, OptionInfo::NumberInfo<uint64_t>{2, opts.arith.arithPivotThreshold, {}, {}}};
    case OptionEnum::POOL_INST:
      return OptionInfo{"pool-inst", {}, opts.quantifiers.poolInstWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.poolInst}};
    case OptionEnum::PORTFOLIO_JOBS:
      return OptionInfo{"portfolio-jobs", {}, opts.driver.portfolioJobsWasSetByUser, OptionInfo::NumberInfo<uint64_t>{1, opts.driver.portfolioJobs, {}, {}}};
    case OptionEnum::PP_ASSERT_MAX_SUB_SIZE:
      return OptionInfo{"pp-assert-max-sub-size", {}, opts.arith.ppAssertMaxSubSizeWasSetByUser, OptionInfo::NumberInfo<uint64_t>{2, opts.arith.ppAssertMaxSubSize, {}, {}}};
    case OptionEnum::PRE_SKOLEM_QUANT:
      return OptionInfo{"pre-skolem-quant", {}, opts.quantifiers.preSkolemQuantWasSetByUser, OptionInfo::ModeInfo{"off", opts.quantifiers.preSkolemQuant, { "agg", "off", "on" }}};
    case OptionEnum::PRE_SKOLEM_QUANT_NESTED:
      return OptionInfo{"pre-skolem-quant-nested", {}, opts.quantifiers.preSkolemQuantNestedWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.preSkolemQuantNested}};
    case OptionEnum::PRENEX_QUANT:
      return OptionInfo{"prenex-quant", {}, opts.quantifiers.prenexQuantWasSetByUser, OptionInfo::ModeInfo{"simple", opts.quantifiers.prenexQuant, { "none", "norm", "simple" }}};
    case OptionEnum::PRENEX_QUANT_USER:
      return OptionInfo{"prenex-quant-user", {}, opts.quantifiers.prenexQuantUserWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.prenexQuantUser}};
    case OptionEnum::PREPROCESS_ONLY:
      return OptionInfo{"preprocess-only", {}, opts.base.preprocessOnlyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.base.preprocessOnly}};
    case OptionEnum::PREREGISTER_MODE:
      return OptionInfo{"preregister-mode", {}, opts.prop.preRegisterModeWasSetByUser, OptionInfo::ModeInfo{"eager", opts.prop.preRegisterMode, { "eager", "lazy" }}};
    case OptionEnum::PRINT_DOT_CLUSTERS:
      return OptionInfo{"print-dot-clusters", {}, opts.proof.printDotClustersWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.printDotClusters}};
    case OptionEnum::PRINT_INST:
      return OptionInfo{"print-inst", {}, opts.quantifiers.printInstModeWasSetByUser, OptionInfo::ModeInfo{"list", opts.quantifiers.printInstMode, { "list", "num" }}};
    case OptionEnum::PRINT_INST_FULL:
      return OptionInfo{"print-inst-full", {}, opts.quantifiers.printInstFullWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.printInstFull}};
    case OptionEnum::PRINT_SUCCESS:
      return OptionInfo{"print-success", {}, opts.driver.printSuccessWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.printSuccess}};
    case OptionEnum::PRINT_UNSAT_CORES_FULL:
      return OptionInfo{"print-unsat-cores-full", {}, opts.smt.printUnsatCoresFullWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.printUnsatCoresFull}};
    case OptionEnum::PRODUCE_ABDUCTS:
      return OptionInfo{"produce-abducts", {}, opts.smt.produceAbductsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceAbducts}};
    case OptionEnum::PRODUCE_ASSERTIONS:
      return OptionInfo{"produce-assertions", {"interactive-mode"}, opts.smt.produceAssertionsWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.smt.produceAssertions}};
    case OptionEnum::PRODUCE_ASSIGNMENTS:
      return OptionInfo{"produce-assignments", {}, opts.smt.produceAssignmentsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceAssignments}};
    case OptionEnum::PRODUCE_DIFFICULTY:
      return OptionInfo{"produce-difficulty", {}, opts.smt.produceDifficultyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceDifficulty}};
    case OptionEnum::PRODUCE_INTERPOLANTS:
      return OptionInfo{"produce-interpolants", {}, opts.smt.produceInterpolantsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceInterpolants}};
    case OptionEnum::PRODUCE_LEARNED_LITERALS:
      return OptionInfo{"produce-learned-literals", {}, opts.smt.produceLearnedLiteralsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceLearnedLiterals}};
    case OptionEnum::PRODUCE_MODELS:
      return OptionInfo{"produce-models", {}, opts.smt.produceModelsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceModels}};
    case OptionEnum::PRODUCE_PROOFS:
      return OptionInfo{"produce-proofs", {}, opts.smt.produceProofsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceProofs}};
    case OptionEnum::PRODUCE_UNSAT_ASSUMPTIONS:
      return OptionInfo{"produce-unsat-assumptions", {}, opts.smt.unsatAssumptionsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.unsatAssumptions}};
    case OptionEnum::PRODUCE_UNSAT_CORES:
      return OptionInfo{"produce-unsat-cores", {}, opts.smt.produceUnsatCoresWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.produceUnsatCores}};
    case OptionEnum::PROOF_ALETHE_RES_PIVOTS:
      return OptionInfo{"proof-alethe-res-pivots", {}, opts.proof.proofAletheResPivotsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.proofAletheResPivots}};
    case OptionEnum::PROOF_ANNOTATE:
      return OptionInfo{"proof-annotate", {}, opts.proof.proofAnnotateWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.proofAnnotate}};
    case OptionEnum::PROOF_CHECK:
      return OptionInfo{"proof-check", {}, opts.proof.proofCheckWasSetByUser, OptionInfo::ModeInfo{"none", opts.proof.proofCheck, { "eager", "eager-simple", "lazy", "none" }}};
    case OptionEnum::PROOF_DOT_DAG:
      return OptionInfo{"proof-dot-dag", {}, opts.proof.printDotAsDAGWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.printDotAsDAG}};
    case OptionEnum::PROOF_FORMAT_MODE:
      return OptionInfo{"proof-format-mode", {}, opts.proof.proofFormatModeWasSetByUser, OptionInfo::ModeInfo{"none", opts.proof.proofFormatMode, { "alethe", "dot", "lfsc", "none", "tptp" }}};
    case OptionEnum::PROOF_GRANULARITY:
      return OptionInfo{"proof-granularity", {}, opts.proof.proofGranularityModeWasSetByUser, OptionInfo::ModeInfo{"macro", opts.proof.proofGranularityMode, { "dsl-rewrite", "macro", "rewrite", "theory-rewrite" }}};
    case OptionEnum::PROOF_MODE:
      return OptionInfo{"proof-mode", {}, opts.smt.proofModeWasSetByUser, OptionInfo::ModeInfo{"off", opts.smt.proofMode, { "full-proof", "off", "pp-only", "sat-proof" }}};
    case OptionEnum::PROOF_PEDANTIC:
      return OptionInfo{"proof-pedantic", {}, opts.proof.proofPedanticWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.proof.proofPedantic, {}, 100}};
    case OptionEnum::PROOF_PP_MERGE:
      return OptionInfo{"proof-pp-merge", {}, opts.proof.proofPpMergeWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.proof.proofPpMerge}};
    case OptionEnum::PROOF_PRINT_CONCLUSION:
      return OptionInfo{"proof-print-conclusion", {}, opts.proof.proofPrintConclusionWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.proofPrintConclusion}};
    case OptionEnum::PROOF_PRUNE_INPUT:
      return OptionInfo{"proof-prune-input", {}, opts.proof.proofPruneInputWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.proof.proofPruneInput}};
    case OptionEnum::PROOF_REWRITE_RCONS_LIMIT:
      return OptionInfo{"proof-rewrite-rcons-limit", {}, opts.proof.proofRewriteRconsRecLimitWasSetByUser, OptionInfo::NumberInfo<int64_t>{5, opts.proof.proofRewriteRconsRecLimit, {}, {}}};
    case OptionEnum::PROP_ROW_LENGTH:
      return OptionInfo{"prop-row-length", {}, opts.arith.arithPropagateMaxLengthWasSetByUser, OptionInfo::NumberInfo<uint64_t>{16, opts.arith.arithPropagateMaxLength, {}, {}}};
    case OptionEnum::PURIFY_TRIGGERS:
      return OptionInfo{"purify-triggers", {}, opts.quantifiers.purifyTriggersWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.purifyTriggers}};
    case OptionEnum::QUANT_ALPHA_EQUIV:
      return OptionInfo{"quant-alpha-equiv", {}, opts.quantifiers.quantAlphaEquivWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.quantAlphaEquiv}};
    case OptionEnum::QUANT_DSPLIT:
      return OptionInfo{"quant-dsplit", {}, opts.quantifiers.quantDynamicSplitWasSetByUser, OptionInfo::ModeInfo{"default", opts.quantifiers.quantDynamicSplit, { "agg", "default", "none" }}};
    case OptionEnum::QUANT_FUN_WD:
      return OptionInfo{"quant-fun-wd", {}, opts.quantifiers.quantFunWellDefinedWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.quantFunWellDefined}};
    case OptionEnum::QUANT_IND:
      return OptionInfo{"quant-ind", {}, opts.quantifiers.quantInductionWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.quantInduction}};
    case OptionEnum::QUANT_REP_MODE:
      return OptionInfo{"quant-rep-mode", {}, opts.quantifiers.quantRepModeWasSetByUser, OptionInfo::ModeInfo{"first", opts.quantifiers.quantRepMode, { "depth", "ee", "first" }}};
    case OptionEnum::QUIET:
      return OptionInfo{"quiet", {}, false, OptionInfo::VoidInfo{}};
    case OptionEnum::RANDOM_FREQ:
      return OptionInfo{"random-freq", {"random-frequency"}, opts.prop.satRandomFreqWasSetByUser, OptionInfo::NumberInfo<double>{0.0, opts.prop.satRandomFreq, 0.0, 1.0}};
    case OptionEnum::RE_ELIM:
      return OptionInfo{"re-elim", {}, opts.strings.regExpElimWasSetByUser, OptionInfo::ModeInfo{"off", opts.strings.regExpElim, { "agg", "off", "on" }}};
    case OptionEnum::RE_INTER_MODE:
      return OptionInfo{"re-inter-mode", {}, opts.strings.stringRegExpInterModeWasSetByUser, OptionInfo::ModeInfo{"none", opts.strings.stringRegExpInterMode, { "all", "constant", "none", "one-constant" }}};
    case OptionEnum::REGISTER_QUANT_BODY_TERMS:
      return OptionInfo{"register-quant-body-terms", {}, opts.quantifiers.registerQuantBodyTermsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.registerQuantBodyTerms}};
    case OptionEnum::RELATIONAL_TRIGGERS:
      return OptionInfo{"relational-triggers", {}, opts.quantifiers.relationalTriggersWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.relationalTriggers}};
    case OptionEnum::RELEVANCE_FILTER:
      return OptionInfo{"relevance-filter", {}, opts.theory.relevanceFilterWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.theory.relevanceFilter}};
    case OptionEnum::RELEVANT_TRIGGERS:
      return OptionInfo{"relevant-triggers", {}, opts.quantifiers.relevantTriggersWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.relevantTriggers}};
    case OptionEnum::REPEAT_SIMP:
      return OptionInfo{"repeat-simp", {}, opts.smt.repeatSimpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.repeatSimp}};
    case OptionEnum::REPLAY_EARLY_CLOSE_DEPTH:
      return OptionInfo{"replay-early-close-depth", {}, opts.arith.replayEarlyCloseDepthsWasSetByUser, OptionInfo::NumberInfo<int64_t>{1, opts.arith.replayEarlyCloseDepths, {}, {}}};
    case OptionEnum::REPLAY_LEMMA_REJECT_CUT:
      return OptionInfo{"replay-lemma-reject-cut", {}, opts.arith.lemmaRejectCutSizeWasSetByUser, OptionInfo::NumberInfo<uint64_t>{25500, opts.arith.lemmaRejectCutSize, {}, {}}};
    case OptionEnum::REPLAY_NUM_ERR_PENALTY:
      return OptionInfo{"replay-num-err-penalty", {}, opts.arith.replayNumericFailurePenaltyWasSetByUser, OptionInfo::NumberInfo<int64_t>{4194304, opts.arith.replayNumericFailurePenalty, {}, {}}};
    case OptionEnum::REPLAY_REJECT_CUT:
      return OptionInfo{"replay-reject-cut", {}, opts.arith.replayRejectCutSizeWasSetByUser, OptionInfo::NumberInfo<uint64_t>{25500, opts.arith.replayRejectCutSize, {}, {}}};
    case OptionEnum::RESTART_INT_BASE:
      return OptionInfo{"restart-int-base", {}, opts.prop.satRestartFirstWasSetByUser, OptionInfo::NumberInfo<uint64_t>{25, opts.prop.satRestartFirst, {}, {}}};
    case OptionEnum::RESTART_INT_INC:
      return OptionInfo{"restart-int-inc", {}, opts.prop.satRestartIncWasSetByUser, OptionInfo::NumberInfo<double>{3.0, opts.prop.satRestartInc, 0.0, {}}};
    case OptionEnum::RESTRICT_PIVOTS:
      return OptionInfo{"restrict-pivots", {}, opts.arith.restrictedPivotsWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.arith.restrictedPivots}};
    case OptionEnum::REVERT_ARITH_MODELS_ON_UNSAT:
      return OptionInfo{"revert-arith-models-on-unsat", {}, opts.arith.revertArithModelsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.revertArithModels}};
    case OptionEnum::RLIMIT:
      return OptionInfo{"rlimit", {}, opts.base.cumulativeResourceLimitWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.base.cumulativeResourceLimit, {}, {}}};
    case OptionEnum::RLIMIT_PER:
      return OptionInfo{"rlimit-per", {"reproducible-resource-limit"}, opts.base.perCallResourceLimitWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.base.perCallResourceLimit, {}, {}}};
    case OptionEnum::RR_TURNS:
      return OptionInfo{"rr-turns", {}, opts.arith.rrTurnsWasSetByUser, OptionInfo::NumberInfo<int64_t>{3, opts.arith.rrTurns, {}, {}}};
    case OptionEnum::RWEIGHT:
      return OptionInfo{"rweight", {}, false, OptionInfo::VoidInfo{}};
    case OptionEnum::SAT_RANDOM_SEED:
      return OptionInfo{"sat-random-seed", {}, opts.prop.satRandomSeedWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.prop.satRandomSeed, {}, {}}};
    case OptionEnum::SE_SOLVE_INT:
      return OptionInfo{"se-solve-int", {}, opts.arith.trySolveIntStandardEffortWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.trySolveIntStandardEffort}};
    case OptionEnum::SEED:
      return OptionInfo{"seed", {}, opts.driver.seedWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.driver.seed, {}, {}}};
    case OptionEnum::SEGV_SPIN:
      return OptionInfo{"segv-spin", {}, opts.driver.segvSpinWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.segvSpin}};
    case OptionEnum::SEMANTIC_CHECKS:
      return OptionInfo{"semantic-checks", {}, opts.parser.semanticChecksWasSetByUser, OptionInfo::ValueInfo<bool>{DO_SEMANTIC_CHECKS_BY_DEFAULT, opts.parser.semanticChecks}};
    case OptionEnum::SEP_MIN_REFINE:
      return OptionInfo{"sep-min-refine", {}, opts.sep.sepMinimalRefineWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.sep.sepMinimalRefine}};
    case OptionEnum::SEP_PRE_SKOLEM_EMP:
      return OptionInfo{"sep-pre-skolem-emp", {}, opts.sep.sepPreSkolemEmpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.sep.sepPreSkolemEmp}};
    case OptionEnum::SEQ_ARRAY:
      return OptionInfo{"seq-array", {}, opts.strings.seqArrayWasSetByUser, OptionInfo::ModeInfo{"none", opts.strings.seqArray, { "eager", "lazy", "none" }}};
    case OptionEnum::SETS_EXT:
      return OptionInfo{"sets-ext", {}, opts.sets.setsExtWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.sets.setsExt}};
    case OptionEnum::SETS_INFER_AS_LEMMAS:
      return OptionInfo{"sets-infer-as-lemmas", {}, opts.sets.setsInferAsLemmasWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.sets.setsInferAsLemmas}};
    case OptionEnum::SETS_PROXY_LEMMAS:
      return OptionInfo{"sets-proxy-lemmas", {}, opts.sets.setsProxyLemmasWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.sets.setsProxyLemmas}};
    case OptionEnum::SHOW_CONFIG:
      return OptionInfo{"show-config", {}, opts.driver.showConfigurationWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.showConfiguration}};
    case OptionEnum::SHOW_TRACE_TAGS:
      return OptionInfo{"show-trace-tags", {}, opts.driver.showTraceTagsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.showTraceTags}};
    case OptionEnum::SIMP_ITE_COMPRESS:
      return OptionInfo{"simp-ite-compress", {}, opts.smt.compressItesWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.compressItes}};
    case OptionEnum::SIMP_WITH_CARE:
      return OptionInfo{"simp-with-care", {}, opts.smt.simplifyWithCareEnabledWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.simplifyWithCareEnabled}};
    case OptionEnum::SIMPLEX_CHECK_PERIOD:
      return OptionInfo{"simplex-check-period", {}, opts.arith.arithSimplexCheckPeriodWasSetByUser, OptionInfo::NumberInfo<uint64_t>{200, opts.arith.arithSimplexCheckPeriod, {}, {}}};
    case OptionEnum::SIMPLIFICATION:
      return OptionInfo{"simplification", {"simplification-mode"}, opts.smt.simplificationModeWasSetByUser, OptionInfo::ModeInfo{"batch", opts.smt.simplificationMode, { "batch", "none" }}};
    case OptionEnum::SIMPLIFICATION_BCP:
      return OptionInfo{"simplification-bcp", {}, opts.smt.simplificationBoolConstPropWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.simplificationBoolConstProp}};
    case OptionEnum::SOI_QE:
      return OptionInfo{"soi-qe", {}, opts.arith.soiQuickExplainWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.soiQuickExplain}};
    case OptionEnum::SOLVE_BV_AS_INT:
      return OptionInfo{"solve-bv-as-int", {}, opts.smt.solveBVAsIntWasSetByUser, OptionInfo::ModeInfo{"off", opts.smt.solveBVAsInt, { "bitwise", "bv", "iand", "off", "sum" }}};
    case OptionEnum::SOLVE_INT_AS_BV:
      return OptionInfo{"solve-int-as-bv", {}, opts.smt.solveIntAsBVWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.smt.solveIntAsBV, {}, 4294967295}};
    case OptionEnum::SOLVE_REAL_AS_INT:
      return OptionInfo{"solve-real-as-int", {}, opts.smt.solveRealAsIntWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.solveRealAsInt}};
    case OptionEnum::SORT_INFERENCE:
      return OptionInfo{"sort-inference", {}, opts.smt.sortInferenceWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.sortInference}};
    case OptionEnum::STANDARD_EFFORT_VARIABLE_ORDER_PIVOTS:
      return OptionInfo{"standard-effort-variable-order-pivots", {}, opts.arith.arithStandardCheckVarOrderPivotsWasSetByUser, OptionInfo::NumberInfo<int64_t>{-1, opts.arith.arithStandardCheckVarOrderPivots, {}, {}}};
    case OptionEnum::STATIC_LEARNING:
      return OptionInfo{"static-learning", {}, opts.smt.staticLearningWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.smt.staticLearning}};
    case OptionEnum::STATS:
      return OptionInfo{"stats", {}, opts.base.statisticsWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.base.statistics}};
    case OptionEnum::STATS_ALL:
      return OptionInfo{"stats-all", {}, opts.base.statisticsAllWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.base.statisticsAll}};
    case OptionEnum::STATS_EVERY_QUERY:
      return OptionInfo{"stats-every-query", {}, opts.base.statisticsEveryQueryWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.base.statisticsEveryQuery}};
    case OptionEnum::STATS_INTERNAL:
      return OptionInfo{"stats-internal", {}, opts.base.statisticsInternalWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.base.statisticsInternal}};
    case OptionEnum::STDIN_INPUT_PER_LINE:
      return OptionInfo{"stdin-input-per-line", {}, opts.driver.stdinInputPerLineWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.driver.stdinInputPerLine}};
    case OptionEnum::STRICT_PARSING:
      return OptionInfo{"strict-parsing", {}, opts.parser.strictParsingWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.parser.strictParsing}};
    case OptionEnum::STRINGS_ALPHA_CARD:
      return OptionInfo{"strings-alpha-card", {}, opts.strings.stringsAlphaCardWasSetByUser, OptionInfo::NumberInfo<uint64_t>{196608, opts.strings.stringsAlphaCard, {}, 196608}};
    case OptionEnum::STRINGS_CHECK_ENTAIL_LEN:
      return OptionInfo{"strings-check-entail-len", {}, opts.strings.stringCheckEntailLenWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringCheckEntailLen}};
    case OptionEnum::STRINGS_CODE_ELIM:
      return OptionInfo{"strings-code-elim", {}, opts.strings.stringsCodeElimWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.strings.stringsCodeElim}};
    case OptionEnum::STRINGS_DEQ_EXT:
      return OptionInfo{"strings-deq-ext", {}, opts.strings.stringsDeqExtWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.strings.stringsDeqExt}};
    case OptionEnum::STRINGS_EAGER_EVAL:
      return OptionInfo{"strings-eager-eval", {}, opts.strings.stringEagerEvalWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringEagerEval}};
    case OptionEnum::STRINGS_EAGER_LEN_RE:
      return OptionInfo{"strings-eager-len-re", {}, opts.strings.stringsEagerLenEntRegexpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.strings.stringsEagerLenEntRegexp}};
    case OptionEnum::STRINGS_EAGER_REG:
      return OptionInfo{"strings-eager-reg", {}, opts.strings.stringEagerRegWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringEagerReg}};
    case OptionEnum::STRINGS_EAGER_SOLVER:
      return OptionInfo{"strings-eager-solver", {}, opts.strings.stringEagerSolverWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringEagerSolver}};
    case OptionEnum::STRINGS_EXP:
      return OptionInfo{"strings-exp", {}, opts.strings.stringExpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.strings.stringExp}};
    case OptionEnum::STRINGS_FF:
      return OptionInfo{"strings-ff", {}, opts.strings.stringFlatFormsWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringFlatForms}};
    case OptionEnum::STRINGS_FMF:
      return OptionInfo{"strings-fmf", {}, opts.strings.stringFMFWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.strings.stringFMF}};
    case OptionEnum::STRINGS_INFER_AS_LEMMAS:
      return OptionInfo{"strings-infer-as-lemmas", {}, opts.strings.stringInferAsLemmasWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.strings.stringInferAsLemmas}};
    case OptionEnum::STRINGS_INFER_SYM:
      return OptionInfo{"strings-infer-sym", {}, opts.strings.stringInferSymWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringInferSym}};
    case OptionEnum::STRINGS_LAZY_PP:
      return OptionInfo{"strings-lazy-pp", {}, opts.strings.stringLazyPreprocWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringLazyPreproc}};
    case OptionEnum::STRINGS_LEN_NORM:
      return OptionInfo{"strings-len-norm", {}, opts.strings.stringLenNormWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringLenNorm}};
    case OptionEnum::STRINGS_MBR:
      return OptionInfo{"strings-mbr", {}, opts.strings.stringModelBasedReductionWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringModelBasedReduction}};
    case OptionEnum::STRINGS_MODEL_MAX_LEN:
      return OptionInfo{"strings-model-max-len", {}, opts.strings.stringsModelMaxLengthWasSetByUser, OptionInfo::NumberInfo<uint64_t>{65536, opts.strings.stringsModelMaxLength, {}, {}}};
    case OptionEnum::STRINGS_PROCESS_LOOP_MODE:
      return OptionInfo{"strings-process-loop-mode", {}, opts.strings.stringProcessLoopModeWasSetByUser, OptionInfo::ModeInfo{"full", opts.strings.stringProcessLoopMode, { "abort", "full", "none", "simple", "simple-abort" }}};
    case OptionEnum::STRINGS_RE_POSC_EAGER:
      return OptionInfo{"strings-re-posc-eager", {}, opts.strings.stringRegexpPosConcatEagerWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.strings.stringRegexpPosConcatEager}};
    case OptionEnum::STRINGS_REGEXP_INCLUSION:
      return OptionInfo{"strings-regexp-inclusion", {}, opts.strings.stringRegexpInclusionWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringRegexpInclusion}};
    case OptionEnum::STRINGS_REXPLAIN_LEMMAS:
      return OptionInfo{"strings-rexplain-lemmas", {}, opts.strings.stringRExplainLemmasWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.strings.stringRExplainLemmas}};
    case OptionEnum::SYGUS:
      return OptionInfo{"sygus", {}, opts.quantifiers.sygusWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygus}};
    case OptionEnum::SYGUS_ABORT_SIZE:
      return OptionInfo{"sygus-abort-size", {}, opts.datatypes.sygusAbortSizeWasSetByUser, OptionInfo::NumberInfo<int64_t>{-1, opts.datatypes.sygusAbortSize, {}, {}}};
    case OptionEnum::SYGUS_ADD_CONST_GRAMMAR:
      return OptionInfo{"sygus-add-const-grammar", {}, opts.quantifiers.sygusAddConstGrammarWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusAddConstGrammar}};
    case OptionEnum::SYGUS_ARG_RELEVANT:
      return OptionInfo{"sygus-arg-relevant", {}, opts.quantifiers.sygusArgRelevantWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusArgRelevant}};
    case OptionEnum::SYGUS_AUTO_UNFOLD:
      return OptionInfo{"sygus-auto-unfold", {}, opts.quantifiers.sygusInvAutoUnfoldWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusInvAutoUnfold}};
    case OptionEnum::SYGUS_BOOL_ITE_RETURN_CONST:
      return OptionInfo{"sygus-bool-ite-return-const", {}, opts.quantifiers.sygusBoolIteReturnConstWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusBoolIteReturnConst}};
    case OptionEnum::SYGUS_CORE_CONNECTIVE:
      return OptionInfo{"sygus-core-connective", {}, opts.quantifiers.sygusCoreConnectiveWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusCoreConnective}};
    case OptionEnum::SYGUS_CREPAIR_ABORT:
      return OptionInfo{"sygus-crepair-abort", {}, opts.quantifiers.sygusConstRepairAbortWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusConstRepairAbort}};
    case OptionEnum::SYGUS_ENUM:
      return OptionInfo{"sygus-enum", {}, opts.quantifiers.sygusEnumModeWasSetByUser, OptionInfo::ModeInfo{"auto", opts.quantifiers.sygusEnumMode, { "auto", "fast", "random", "smart", "var-agnostic" }}};
    case OptionEnum::SYGUS_ENUM_FAST_NUM_CONSTS:
      return OptionInfo{"sygus-enum-fast-num-consts", {}, opts.quantifiers.sygusEnumFastNumConstsWasSetByUser, OptionInfo::NumberInfo<uint64_t>{5, opts.quantifiers.sygusEnumFastNumConsts, {}, {}}};
    case OptionEnum::SYGUS_ENUM_RANDOM_P:
      return OptionInfo{"sygus-enum-random-p", {}, opts.quantifiers.sygusEnumRandomPWasSetByUser, OptionInfo::NumberInfo<double>{0.5, opts.quantifiers.sygusEnumRandomP, 0.0, 1.0}};
    case OptionEnum::SYGUS_EVAL_UNFOLD:
      return OptionInfo{"sygus-eval-unfold", {}, opts.quantifiers.sygusEvalUnfoldModeWasSetByUser, OptionInfo::ModeInfo{"single-bool", opts.quantifiers.sygusEvalUnfoldMode, { "multi", "none", "single", "single-bool" }}};
    case OptionEnum::SYGUS_EXPR_MINER_CHECK_TIMEOUT:
      return OptionInfo{"sygus-expr-miner-check-timeout", {}, opts.quantifiers.sygusExprMinerCheckTimeoutWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.quantifiers.sygusExprMinerCheckTimeout, {}, {}}};
    case OptionEnum::SYGUS_FAIR:
      return OptionInfo{"sygus-fair", {}, opts.datatypes.sygusFairWasSetByUser, OptionInfo::ModeInfo{"dt-size", opts.datatypes.sygusFair, { "direct", "dt-height-bound", "dt-size", "dt-size-bound", "none" }}};
    case OptionEnum::SYGUS_FAIR_MAX:
      return OptionInfo{"sygus-fair-max", {}, opts.datatypes.sygusFairMaxWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.sygusFairMax}};
    case OptionEnum::SYGUS_FILTER_SOL:
      return OptionInfo{"sygus-filter-sol", {}, opts.quantifiers.sygusFilterSolModeWasSetByUser, OptionInfo::ModeInfo{"none", opts.quantifiers.sygusFilterSolMode, { "none", "strong", "weak" }}};
    case OptionEnum::SYGUS_FILTER_SOL_REV:
      return OptionInfo{"sygus-filter-sol-rev", {}, opts.quantifiers.sygusFilterSolRevSubsumeWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusFilterSolRevSubsume}};
    case OptionEnum::SYGUS_GRAMMAR_CONS:
      return OptionInfo{"sygus-grammar-cons", {}, opts.quantifiers.sygusGrammarConsModeWasSetByUser, OptionInfo::ModeInfo{"simple", opts.quantifiers.sygusGrammarConsMode, { "any-const", "any-term", "any-term-concise", "simple" }}};
    case OptionEnum::SYGUS_GRAMMAR_NORM:
      return OptionInfo{"sygus-grammar-norm", {}, opts.quantifiers.sygusGrammarNormWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusGrammarNorm}};
    case OptionEnum::SYGUS_INFERENCE:
      return OptionInfo{"sygus-inference", {}, opts.quantifiers.sygusInferenceWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusInference}};
    case OptionEnum::SYGUS_INST:
      return OptionInfo{"sygus-inst", {}, opts.quantifiers.sygusInstWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusInst}};
    case OptionEnum::SYGUS_INST_MODE:
      return OptionInfo{"sygus-inst-mode", {}, opts.quantifiers.sygusInstModeWasSetByUser, OptionInfo::ModeInfo{"priority-inst", opts.quantifiers.sygusInstMode, { "interleave", "priority-eval", "priority-inst" }}};
    case OptionEnum::SYGUS_INST_SCOPE:
      return OptionInfo{"sygus-inst-scope", {}, opts.quantifiers.sygusInstScopeWasSetByUser, OptionInfo::ModeInfo{"in", opts.quantifiers.sygusInstScope, { "both", "in", "out" }}};
    case OptionEnum::SYGUS_INST_TERM_SEL:
      return OptionInfo{"sygus-inst-term-sel", {}, opts.quantifiers.sygusInstTermSelWasSetByUser, OptionInfo::ModeInfo{"min", opts.quantifiers.sygusInstTermSel, { "both", "max", "min" }}};
    case OptionEnum::SYGUS_INV_TEMPL:
      return OptionInfo{"sygus-inv-templ", {}, opts.quantifiers.sygusInvTemplModeWasSetByUser, OptionInfo::ModeInfo{"post", opts.quantifiers.sygusInvTemplMode, { "none", "post", "pre" }}};
    case OptionEnum::SYGUS_INV_TEMPL_WHEN_SG:
      return OptionInfo{"sygus-inv-templ-when-sg", {}, opts.quantifiers.sygusInvTemplWhenSyntaxWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusInvTemplWhenSyntax}};
    case OptionEnum::SYGUS_MIN_GRAMMAR:
      return OptionInfo{"sygus-min-grammar", {}, opts.quantifiers.sygusMinGrammarWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusMinGrammar}};
    case OptionEnum::SYGUS_OUT:
      return OptionInfo{"sygus-out", {}, opts.quantifiers.sygusOutWasSetByUser, OptionInfo::ModeInfo{"sygus-standard", opts.quantifiers.sygusOut, { "status", "status-and-def", "sygus-standard" }}};
    case OptionEnum::SYGUS_PBE:
      return OptionInfo{"sygus-pbe", {}, opts.quantifiers.sygusUnifPbeWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusUnifPbe}};
    case OptionEnum::SYGUS_PBE_MULTI_FAIR:
      return OptionInfo{"sygus-pbe-multi-fair", {}, opts.quantifiers.sygusPbeMultiFairWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusPbeMultiFair}};
    case OptionEnum::SYGUS_PBE_MULTI_FAIR_DIFF:
      return OptionInfo{"sygus-pbe-multi-fair-diff", {}, opts.quantifiers.sygusPbeMultiFairDiffWasSetByUser, OptionInfo::NumberInfo<int64_t>{0, opts.quantifiers.sygusPbeMultiFairDiff, {}, {}}};
    case OptionEnum::SYGUS_QE_PREPROC:
      return OptionInfo{"sygus-qe-preproc", {}, opts.quantifiers.sygusQePreprocWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusQePreproc}};
    case OptionEnum::SYGUS_QUERY_GEN:
      return OptionInfo{"sygus-query-gen", {}, opts.quantifiers.sygusQueryGenWasSetByUser, OptionInfo::ModeInfo{"none", opts.quantifiers.sygusQueryGen, { "basic", "none", "sample-sat", "unsat" }}};
    case OptionEnum::SYGUS_QUERY_GEN_DUMP_FILES:
      return OptionInfo{"sygus-query-gen-dump-files", {}, opts.quantifiers.sygusQueryGenDumpFilesWasSetByUser, OptionInfo::ModeInfo{"none", opts.quantifiers.sygusQueryGenDumpFiles, { "all", "none", "unsolved" }}};
    case OptionEnum::SYGUS_QUERY_GEN_THRESH:
      return OptionInfo{"sygus-query-gen-thresh", {}, opts.quantifiers.sygusQueryGenThreshWasSetByUser, OptionInfo::NumberInfo<uint64_t>{5, opts.quantifiers.sygusQueryGenThresh, {}, {}}};
    case OptionEnum::SYGUS_REC_FUN:
      return OptionInfo{"sygus-rec-fun", {}, opts.quantifiers.sygusRecFunWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusRecFun}};
    case OptionEnum::SYGUS_REC_FUN_EVAL_LIMIT:
      return OptionInfo{"sygus-rec-fun-eval-limit", {}, opts.quantifiers.sygusRecFunEvalLimitWasSetByUser, OptionInfo::NumberInfo<uint64_t>{1000, opts.quantifiers.sygusRecFunEvalLimit, {}, {}}};
    case OptionEnum::SYGUS_REPAIR_CONST:
      return OptionInfo{"sygus-repair-const", {}, opts.quantifiers.sygusRepairConstWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRepairConst}};
    case OptionEnum::SYGUS_REPAIR_CONST_TIMEOUT:
      return OptionInfo{"sygus-repair-const-timeout", {}, opts.quantifiers.sygusRepairConstTimeoutWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.quantifiers.sygusRepairConstTimeout, {}, {}}};
    case OptionEnum::SYGUS_REWRITER:
      return OptionInfo{"sygus-rewriter", {}, opts.datatypes.sygusRewriterWasSetByUser, OptionInfo::ModeInfo{"extended", opts.datatypes.sygusRewriter, { "basic", "extended", "none" }}};
    case OptionEnum::SYGUS_RR_SYNTH:
      return OptionInfo{"sygus-rr-synth", {}, opts.quantifiers.sygusRewSynthWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRewSynth}};
    case OptionEnum::SYGUS_RR_SYNTH_ACCEL:
      return OptionInfo{"sygus-rr-synth-accel", {}, opts.quantifiers.sygusRewSynthAccelWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRewSynthAccel}};
    case OptionEnum::SYGUS_RR_SYNTH_CHECK:
      return OptionInfo{"sygus-rr-synth-check", {}, opts.quantifiers.sygusRewSynthCheckWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusRewSynthCheck}};
    case OptionEnum::SYGUS_RR_SYNTH_FILTER_CONG:
      return OptionInfo{"sygus-rr-synth-filter-cong", {}, opts.quantifiers.sygusRewSynthFilterCongWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusRewSynthFilterCong}};
    case OptionEnum::SYGUS_RR_SYNTH_FILTER_MATCH:
      return OptionInfo{"sygus-rr-synth-filter-match", {}, opts.quantifiers.sygusRewSynthFilterMatchWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusRewSynthFilterMatch}};
    case OptionEnum::SYGUS_RR_SYNTH_FILTER_NL:
      return OptionInfo{"sygus-rr-synth-filter-nl", {}, opts.quantifiers.sygusRewSynthFilterNonLinearWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRewSynthFilterNonLinear}};
    case OptionEnum::SYGUS_RR_SYNTH_FILTER_ORDER:
      return OptionInfo{"sygus-rr-synth-filter-order", {}, opts.quantifiers.sygusRewSynthFilterOrderWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusRewSynthFilterOrder}};
    case OptionEnum::SYGUS_RR_SYNTH_INPUT:
      return OptionInfo{"sygus-rr-synth-input", {}, opts.quantifiers.sygusRewSynthInputWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRewSynthInput}};
    case OptionEnum::SYGUS_RR_SYNTH_INPUT_NVARS:
      return OptionInfo{"sygus-rr-synth-input-nvars", {}, opts.quantifiers.sygusRewSynthInputNVarsWasSetByUser, OptionInfo::NumberInfo<int64_t>{3, opts.quantifiers.sygusRewSynthInputNVars, {}, {}}};
    case OptionEnum::SYGUS_RR_SYNTH_INPUT_USE_BOOL:
      return OptionInfo{"sygus-rr-synth-input-use-bool", {}, opts.quantifiers.sygusRewSynthInputUseBoolWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRewSynthInputUseBool}};
    case OptionEnum::SYGUS_RR_SYNTH_REC:
      return OptionInfo{"sygus-rr-synth-rec", {}, opts.quantifiers.sygusRewSynthRecWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRewSynthRec}};
    case OptionEnum::SYGUS_RR_VERIFY:
      return OptionInfo{"sygus-rr-verify", {}, opts.quantifiers.sygusRewVerifyWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusRewVerify}};
    case OptionEnum::SYGUS_SAMPLE_FP_UNIFORM:
      return OptionInfo{"sygus-sample-fp-uniform", {}, opts.quantifiers.sygusSampleFpUniformWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusSampleFpUniform}};
    case OptionEnum::SYGUS_SAMPLE_GRAMMAR:
      return OptionInfo{"sygus-sample-grammar", {}, opts.quantifiers.sygusSampleGrammarWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusSampleGrammar}};
    case OptionEnum::SYGUS_SAMPLES:
      return OptionInfo{"sygus-samples", {}, opts.quantifiers.sygusSamplesWasSetByUser, OptionInfo::NumberInfo<int64_t>{1000, opts.quantifiers.sygusSamples, {}, {}}};
    case OptionEnum::SYGUS_SI:
      return OptionInfo{"sygus-si", {}, opts.quantifiers.cegqiSingleInvModeWasSetByUser, OptionInfo::ModeInfo{"none", opts.quantifiers.cegqiSingleInvMode, { "all", "none", "use" }}};
    case OptionEnum::SYGUS_SI_ABORT:
      return OptionInfo{"sygus-si-abort", {}, opts.quantifiers.cegqiSingleInvAbortWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.cegqiSingleInvAbort}};
    case OptionEnum::SYGUS_SI_RCONS:
      return OptionInfo{"sygus-si-rcons", {}, opts.quantifiers.cegqiSingleInvReconstructWasSetByUser, OptionInfo::ModeInfo{"all", opts.quantifiers.cegqiSingleInvReconstruct, { "all", "all-limit", "none", "try" }}};
    case OptionEnum::SYGUS_SI_RCONS_LIMIT:
      return OptionInfo{"sygus-si-rcons-limit", {}, opts.quantifiers.cegqiSingleInvReconstructLimitWasSetByUser, OptionInfo::NumberInfo<int64_t>{10000, opts.quantifiers.cegqiSingleInvReconstructLimit, {}, {}}};
    case OptionEnum::SYGUS_SIMPLE_SYM_BREAK:
      return OptionInfo{"sygus-simple-sym-break", {}, opts.datatypes.sygusSimpleSymBreakWasSetByUser, OptionInfo::ModeInfo{"agg", opts.datatypes.sygusSimpleSymBreak, { "agg", "basic", "none" }}};
    case OptionEnum::SYGUS_STREAM:
      return OptionInfo{"sygus-stream", {}, opts.quantifiers.sygusStreamWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusStream}};
    case OptionEnum::SYGUS_SYM_BREAK_LAZY:
      return OptionInfo{"sygus-sym-break-lazy", {}, opts.datatypes.sygusSymBreakLazyWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.sygusSymBreakLazy}};
    case OptionEnum::SYGUS_SYM_BREAK_PBE:
      return OptionInfo{"sygus-sym-break-pbe", {}, opts.datatypes.sygusSymBreakPbeWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.sygusSymBreakPbe}};
    case OptionEnum::SYGUS_SYM_BREAK_RLV:
      return OptionInfo{"sygus-sym-break-rlv", {}, opts.datatypes.sygusSymBreakRlvWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.datatypes.sygusSymBreakRlv}};
    case OptionEnum::SYGUS_UNIF_COND_INDEPENDENT_NO_REPEAT_SOL:
      return OptionInfo{"sygus-unif-cond-independent-no-repeat-sol", {}, opts.quantifiers.sygusUnifCondIndNoRepeatSolWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.sygusUnifCondIndNoRepeatSol}};
    case OptionEnum::SYGUS_UNIF_PI:
      return OptionInfo{"sygus-unif-pi", {}, opts.quantifiers.sygusUnifPiWasSetByUser, OptionInfo::ModeInfo{"none", opts.quantifiers.sygusUnifPi, { "complete", "cond-enum", "cond-enum-igain", "none" }}};
    case OptionEnum::SYGUS_UNIF_SHUFFLE_COND:
      return OptionInfo{"sygus-unif-shuffle-cond", {}, opts.quantifiers.sygusUnifShuffleCondWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.quantifiers.sygusUnifShuffleCond}};
    case OptionEnum::SYGUS_VERIFY_INST_MAX_ROUNDS:
      return OptionInfo{"sygus-verify-inst-max-rounds", {}, opts.quantifiers.sygusVerifyInstMaxRoundsWasSetByUser, OptionInfo::NumberInfo<int64_t>{10, opts.quantifiers.sygusVerifyInstMaxRounds, {}, {}}};
    case OptionEnum::SYGUS_VERIFY_TIMEOUT:
      return OptionInfo{"sygus-verify-timeout", {}, opts.quantifiers.sygusVerifyTimeoutWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.quantifiers.sygusVerifyTimeout, {}, {}}};
    case OptionEnum::SYMMETRY_BREAKER:
      return OptionInfo{"symmetry-breaker", {}, opts.uf.ufSymmetryBreakerWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.uf.ufSymmetryBreaker}};
    case OptionEnum::TC_MODE:
      return OptionInfo{"tc-mode", {}, opts.theory.tcModeWasSetByUser, OptionInfo::ModeInfo{"care-graph", opts.theory.tcMode, { "care-graph" }}};
    case OptionEnum::TERM_DB_CD:
      return OptionInfo{"term-db-cd", {}, opts.quantifiers.termDbCdWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.termDbCd}};
    case OptionEnum::TERM_DB_MODE:
      return OptionInfo{"term-db-mode", {}, opts.quantifiers.termDbModeWasSetByUser, OptionInfo::ModeInfo{"all", opts.quantifiers.termDbMode, { "all", "relevant" }}};
    case OptionEnum::THEORYOF_MODE:
      return OptionInfo{"theoryof-mode", {}, opts.theory.theoryOfModeWasSetByUser, OptionInfo::ModeInfo{"type", opts.theory.theoryOfMode, { "term", "type" }}};
    case OptionEnum::TLIMIT:
      return OptionInfo{"tlimit", {}, opts.base.cumulativeMillisecondLimitWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.base.cumulativeMillisecondLimit, {}, {}}};
    case OptionEnum::TLIMIT_PER:
      return OptionInfo{"tlimit-per", {}, opts.base.perCallMillisecondLimitWasSetByUser, OptionInfo::NumberInfo<uint64_t>{0, opts.base.perCallMillisecondLimit, {}, {}}};
    case OptionEnum::TRACE:
      return OptionInfo{"trace", {}, false, OptionInfo::VoidInfo{}};
    case OptionEnum::TRIGGER_ACTIVE_SEL:
      return OptionInfo{"trigger-active-sel", {}, opts.quantifiers.triggerActiveSelModeWasSetByUser, OptionInfo::ModeInfo{"all", opts.quantifiers.triggerActiveSelMode, { "all", "max", "min" }}};
    case OptionEnum::TRIGGER_SEL:
      return OptionInfo{"trigger-sel", {}, opts.quantifiers.triggerSelModeWasSetByUser, OptionInfo::ModeInfo{"min", opts.quantifiers.triggerSelMode, { "all", "max", "min", "min-s-all", "min-s-max" }}};
    case OptionEnum::TYPE_CHECKING:
      return OptionInfo{"type-checking", {}, opts.expr.typeCheckingWasSetByUser, OptionInfo::ValueInfo<bool>{DO_SEMANTIC_CHECKS_BY_DEFAULT, opts.expr.typeChecking}};
    case OptionEnum::UF_HO_EXT:
      return OptionInfo{"uf-ho-ext", {}, opts.uf.ufHoExtWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.uf.ufHoExt}};
    case OptionEnum::UF_LAZY_LL:
      return OptionInfo{"uf-lazy-ll", {}, opts.uf.ufHoLazyLambdaLiftWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.uf.ufHoLazyLambdaLift}};
    case OptionEnum::UF_SS:
      return OptionInfo{"uf-ss", {}, opts.uf.ufssModeWasSetByUser, OptionInfo::ModeInfo{"full", opts.uf.ufssMode, { "full", "no-minimal", "none" }}};
    case OptionEnum::UF_SS_ABORT_CARD:
      return OptionInfo{"uf-ss-abort-card", {}, opts.uf.ufssAbortCardinalityWasSetByUser, OptionInfo::NumberInfo<int64_t>{-1, opts.uf.ufssAbortCardinality, {}, {}}};
    case OptionEnum::UF_SS_FAIR:
      return OptionInfo{"uf-ss-fair", {}, opts.uf.ufssFairnessWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.uf.ufssFairness}};
    case OptionEnum::UF_SS_FAIR_MONOTONE:
      return OptionInfo{"uf-ss-fair-monotone", {}, opts.uf.ufssFairnessMonotoneWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.uf.ufssFairnessMonotone}};
    case OptionEnum::UNATE_LEMMAS:
      return OptionInfo{"unate-lemmas", {}, opts.arith.arithUnateLemmaModeWasSetByUser, OptionInfo::ModeInfo{"all", opts.arith.arithUnateLemmaMode, { "all", "eqs", "ineqs", "none" }}};
    case OptionEnum::UNCONSTRAINED_SIMP:
      return OptionInfo{"unconstrained-simp", {}, opts.smt.unconstrainedSimpWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.smt.unconstrainedSimp}};
    case OptionEnum::UNSAT_CORES_MODE:
      return OptionInfo{"unsat-cores-mode", {}, opts.smt.unsatCoresModeWasSetByUser, OptionInfo::ModeInfo{"off", opts.smt.unsatCoresMode, { "assumptions", "off", "sat-proof" }}};
    case OptionEnum::USE_APPROX:
      return OptionInfo{"use-approx", {}, opts.arith.useApproxWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.useApprox}};
    case OptionEnum::USE_FCSIMPLEX:
      return OptionInfo{"use-fcsimplex", {}, opts.arith.useFCWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.useFC}};
    case OptionEnum::USE_PORTFOLIO:
      return OptionInfo{"use-portfolio", {}, opts.driver.usePortfolioWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.usePortfolio}};
    case OptionEnum::USE_SOI:
      return OptionInfo{"use-soi", {}, opts.arith.useSOIWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.arith.useSOI}};
    case OptionEnum::USER_PAT:
      return OptionInfo{"user-pat", {}, opts.quantifiers.userPatternsQuantWasSetByUser, OptionInfo::ModeInfo{"trust", opts.quantifiers.userPatternsQuant, { "ignore", "interleave", "resort", "strict", "trust", "use" }}};
    case OptionEnum::USER_POOL:
      return OptionInfo{"user-pool", {}, opts.quantifiers.userPoolQuantWasSetByUser, OptionInfo::ModeInfo{"trust", opts.quantifiers.userPoolQuant, { "ignore", "trust", "use" }}};
    case OptionEnum::VAR_ELIM_QUANT:
      return OptionInfo{"var-elim-quant", {}, opts.quantifiers.varElimQuantWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.varElimQuant}};
    case OptionEnum::VAR_INEQ_ELIM_QUANT:
      return OptionInfo{"var-ineq-elim-quant", {}, opts.quantifiers.varIneqElimQuantWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.quantifiers.varIneqElimQuant}};
    case OptionEnum::VERBOSE:
      return OptionInfo{"verbose", {}, false, OptionInfo::VoidInfo{}};
    case OptionEnum::VERBOSITY:
      return OptionInfo{"verbosity", {}, opts.base.verbosityWasSetByUser, OptionInfo::NumberInfo<int64_t>{0, opts.base.verbosity, {}, {}}};
    case OptionEnum::VERSION:
      return OptionInfo{"version", {}, opts.driver.showVersionWasSetByUser, OptionInfo::ValueInfo<bool>{false, opts.driver.showVersion}};
    case OptionEnum::WF_CHECKING:
      return OptionInfo{"wf-checking", {}, opts.expr.wellFormedCheckingWasSetByUser, OptionInfo::ValueInfo<bool>{true, opts.expr.wellFormedChecking}};
    case OptionEnum::WRITE_PARTITIONS_TO:
      return OptionInfo{"write-partitions-to", {"partitions-out"}, opts.parallel.partitionsOutWasSetByUser, OptionInfo::VoidInfo{}};
  }
  // clang-format on
  return OptionInfo{"", {}, false, OptionInfo::VoidInfo{}};
}

#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

}  // namespace cvc5::internal::options
