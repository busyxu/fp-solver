/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Options utilities used in the driver.
 */

#include "main/options.h"

#if !defined(_BSD_SOURCE) && defined(__MINGW32__) && !defined(__MINGW64__)
// force use of optreset; mingw32 croaks on argv-switching otherwise
#include "base/cvc5config.h"
#define _BSD_SOURCE
#undef HAVE_DECL_OPTRESET
#define HAVE_DECL_OPTRESET 1
#define CVC5_IS_NOT_REALLY_BSD
#endif /* !_BSD_SOURCE && __MINGW32__ && !__MINGW64__ */

#ifdef __MINGW64__
extern int optreset;
#endif /* __MINGW64__ */

#include <getopt.h>

// clean up
#ifdef CVC5_IS_NOT_REALLY_BSD
#  undef _BSD_SOURCE
#endif /* CVC5_IS_NOT_REALLY_BSD */

#include "base/check.h"
#include "base/output.h"
#include "options/option_exception.h"
#include "util/didyoumean.h"

#include <cstring>
#include <iostream>
#include <limits>

namespace cvc5::main {

using namespace cvc5::internal;

// clang-format off
static const std::string commonOptionsDescription =
R"FOOBAR(Most commonly-used cvc5 options:
  --incremental | -i     enable incremental solving [*]
  --lang=LANG | --input-language=LANG | -L LANG
                         force input language (default is "auto"; see --lang
                         help)
  --output=TAG | -o TAG  Enable output tag.
  --parse-only           exit after parsing input [*]
  --preprocess-only      exit after preprocessing input [*]
  --quiet | -q           decrease verbosity (may be repeated)
  --rlimit=N             set resource limit
  --rlimit-per=N | --reproducible-resource-limit=N
                         set resource limit per query
  --stats                give statistics on exit [*]
  --tlimit=MS            set time limit in milliseconds of wall clock time
  --tlimit-per=MS        set time limit per query in milliseconds
  --verbose | -v         increase verbosity (may be repeated)
  --verbosity=N          the verbosity level of cvc5
  --copyright            show cvc5 copyright information
  --help | -h            full command line reference
  --interactive          force interactive shell/non-interactive mode [*]
  --print-success        print the "success" output required of SMT-LIBv2 [*]
  --seed=N | -s N        seed for random number generator
  --show-config          show cvc5 static configuration
  --version | -V         identify this cvc5 binary
  --force-logic=LOGIC    set the logic, and override all further user attempts
                         to change it
  --strict-parsing       be less tolerant of non-conforming inputs [*]
  --dag-thresh=N         dagify common subexprs appearing > N times (1 ==
                         default, 0 == don't dagify)
  --output-lang=LANG | --output-language=LANG
                         force output language (default is "auto"; see
                         --output-lang help)
  --print-inst=MODE      print format for printing instantiations
  --check-models         after SAT/INVALID/UNKNOWN, check that the generated
                         model satisfies user assertions [*]
  --produce-models | -m  support the get-value and get-model commands [*]
)FOOBAR";

static const std::string additionalOptionsDescription =
R"FOOBAR(Additional cvc5 options:

From the Arithmetic Theory module:
  --approx-branch-depth=N
                         maximum branch depth the approximate solver is allowed
                         to take (EXPERTS only)
  --arith-brab           whether to use simple rounding, similar to a unit-cube
                         test, for integers [*]
  --arith-eq-solver      whether to use the equality solver in the theory of
                         arithmetic (EXPERTS only) [*]
  --arith-no-partial-fun do not use partial function semantics for arithmetic
                         (not SMT LIB compliant) (EXPERTS only) [*]
  --arith-prop=MODE      turns on arithmetic propagation (default is 'old', see
                         --arith-prop=help) (EXPERTS only)
  --arith-prop-clauses=N rows shorter than this are propagated as clauses
                         (EXPERTS only)
  --arith-rewrite-equalities
                         turns on the preprocessing rewrite turning equalities
                         into a conjunction of inequalities [*]
  --arith-static-learning
                         do arithmetic static learning for ite terms based on
                         bounds when static learning is enabled [*]
  --collect-pivot-stats  collect the pivot history (EXPERTS only) [*]
  --cut-all-bounded      turns on the integer solving step of periodically
                         cutting all integer variables that have both upper and
                         lower bounds (EXPERTS only) [*]
  --dio-decomps          let skolem variables for integer divisibility
                         constraints leak from the dio solver (EXPERTS only) [*]
  --dio-solver           turns on Linear Diophantine Equation solver (Griggio,
                         JSAT 2012) (EXPERTS only) [*]
  --dio-turns=N          turns in a row dio solver cutting gets (EXPERTS only)
  --error-selection-rule=RULE
                         change the pivot rule for the basic variable (default
                         is 'min', see --pivot-rule help) (EXPERTS only)
  --fc-penalties         turns on degenerate pivot penalties (EXPERTS only) [*]
  --heuristic-pivots=N   the number of times to apply the heuristic pivot rule;
                         if N < 0, this defaults to the number of variables; if
                         this is unset, this is tuned by the logic selection
                         (EXPERTS only)
  --lemmas-on-replay-failure
                         attempt to use external lemmas if approximate solve
                         integer failed (EXPERTS only) [*]
  --maxCutsInContext=N   maximum cuts in a given context before signalling a
                         restart (EXPERTS only)
  --miplib-trick         turns on the preprocessing step of attempting to infer
                         bounds on miplib problems (EXPERTS only) [*]
  --miplib-trick-subs=N  do substitution for miplib 'tmp' vars if defined in <=
                         N eliminated vars (EXPERTS only)
  --new-prop             use the new row propagation system (EXPERTS only) [*]
  --nl-cov               whether to use the cylindrical algebraic coverings
                         solver for non-linear arithmetic [*]
  --nl-cov-force         forces using the cylindrical algebraic coverings
                         solver, even in cases where it is possibly not safe to
                         do so (EXPERTS only) [*]
  --nl-cov-lift=MODE     choose the Coverings lifting mode (EXPERTS only)
  --nl-cov-linear-model=MODE
                         whether to use the linear model as initial guess for
                         the cylindrical algebraic coverings solver
  --nl-cov-proj=MODE     choose the Coverings projection operator (EXPERTS only)
  --nl-cov-prune         whether to prune intervals more agressively (EXPERTS
                         only) [*]
  --nl-cov-var-elim      whether to eliminate variables using equalities before
                         going into the cylindrical algebraic coverings solver.
                         It can not be used when producing proofs right now.
                         (EXPERTS only) [*]
  --nl-ext=MODE          incremental linearization approach to non-linear
  --nl-ext-ent-conf      check for entailed conflicts in non-linear solver
                         (EXPERTS only) [*]
  --nl-ext-factor        use factoring inference in non-linear incremental
                         linearization solver [*]
  --nl-ext-inc-prec      whether to increment the precision for irrational
                         function constraints (EXPERTS only) [*]
  --nl-ext-purify        purify non-linear terms at preprocess (EXPERTS only)
                         [*]
  --nl-ext-rbound        use resolution-style inference for inferring new bounds
                         in non-linear incremental linearization solver (EXPERTS
                         only) [*]
  --nl-ext-rewrite       do context-dependent simplification based on rewrites
                         in non-linear solver [*]
  --nl-ext-split-zero    initial splits on zero for all variables (EXPERTS only)
                         [*]
  --nl-ext-tf-taylor-deg=N
                         initial degree of polynomials for Taylor approximation
                         (EXPERTS only)
  --nl-ext-tf-tplanes    use non-terminating tangent plane strategy for
                         transcendental functions for non-linear incremental
                         linearization solver [*]
  --nl-ext-tplanes       use non-terminating tangent plane strategy for
                         non-linear incremental linearization solver [*]
  --nl-ext-tplanes-interleave
                         interleave tangent plane strategy for non-linear
                         incremental linearization solver [*]
  --nl-icp               whether to use ICP-style propagations for non-linear
                         arithmetic (EXPERTS only) [*]
  --nl-rlv=MODE          choose mode for using relevance of assertions in
                         non-linear arithmetic (EXPERTS only)
  --nl-rlv-assert-bounds use bound inference utility to prune when an assertion
                         is entailed by another (EXPERTS only) [*]
  --pb-rewrites          apply pseudo boolean rewrites (EXPERTS only) [*]
  --pivot-threshold=N    sets the number of pivots using --pivot-rule per basic
                         variable per simplex instance before using variable
                         order (EXPERTS only)
  --pp-assert-max-sub-size=N
                         threshold for substituting an equality in ppAssert
                         (EXPERTS only)
  --prop-row-length=N    sets the maximum row length to be used in propagation
                         (EXPERTS only)
  --replay-early-close-depth=N
                         multiples of the depths to try to close the approx log
                         eagerly (EXPERTS only)
  --replay-lemma-reject-cut=N
                         maximum complexity of any coefficient while outputting
                         replaying cut lemmas (EXPERTS only)
  --replay-num-err-penalty=N
                         number of solve integer attempts to skips after a
                         numeric failure (EXPERTS only)
  --replay-reject-cut=N  maximum complexity of any coefficient while replaying
                         cuts (EXPERTS only)
  --restrict-pivots      have a pivot cap for simplex at effort levels below
                         fullEffort (EXPERTS only) [*]
  --revert-arith-models-on-unsat
                         revert the arithmetic model to a known safe model on
                         unsat if one is cached (EXPERTS only) [*]
  --rr-turns=N           round robin turn (EXPERTS only)
  --se-solve-int         attempt to use the approximate solve integer method on
                         standard effort (EXPERTS only) [*]
  --simplex-check-period=N
                         the number of pivots to do in simplex before rechecking
                         for a conflict on all variables (EXPERTS only)
  --soi-qe               use quick explain to minimize the sum of infeasibility
                         conflicts (EXPERTS only) [*]
  --standard-effort-variable-order-pivots=N
                         limits the number of pivots in a single invocation of
                         check() at a non-full effort level using Bland's pivot
                         rule (EXPERTS only)
  --unate-lemmas=MODE    determines which lemmas to add before solving (default
                         is 'all', see --unate-lemmas=help) (EXPERTS only)
  --use-approx           attempt to use an approximate solver (EXPERTS only) [*]
  --use-fcsimplex        use focusing and converging simplex (FMCAD 2013
                         submission) (EXPERTS only) [*]
  --use-soi              use sum of infeasibility simplex (FMCAD 2013
                         submission) (EXPERTS only) [*]

From the Arrays Theory module:
  --arrays-eager-index   turn on eager index splitting for generated array
                         lemmas [*]
  --arrays-eager-lemmas  turn on eager lemma generation for arrays (EXPERTS
                         only) [*]
  --arrays-exp           enable experimental features in the theory of arrays
                         (EXPERTS only) [*]
  --arrays-optimize-linear
                         turn on optimization for linear array terms (see de
                         Moura FMCAD 09 arrays paper) (EXPERTS only) [*]
  --arrays-prop=N        propagation effort for arrays: 0 is none, 1 is some, 2
                         is full (EXPERTS only)
  --arrays-reduce-sharing
                         use model information to reduce size of care graph for
                         arrays (EXPERTS only) [*]
  --arrays-weak-equiv    use algorithm from Christ/Hoenicke (SMT 2014) (EXPERTS
                         only) [*]

From the Base module:
  --err=erroutput | --diagnostic-output-channel=erroutput
                         Set the error (or diagnostic) output channel. Writes to
                         stderr for "stderr" or "--", stdout for "stdout" or the
                         given filename otherwise. (EXPERTS only)
  --in=input             Set the error (or diagnostic) output channel. Reads
                         from stdin for "stdin" or "--" and the given filename
                         otherwise. (EXPERTS only)
  --out=output | --regular-output-channel=output
                         Set the error (or diagnostic) output channel. Writes to
                         stdout for "stdout" or "--", stderr for "stderr" or the
                         given filename otherwise. (EXPERTS only)
  --rweight=VAL=N        set a single resource weight (EXPERTS only)
  --stats-all            print unchanged (defaulted) statistics as well (EXPERTS
                         only) [*]
  --stats-every-query    in incremental mode, print stats after every
                         satisfiability or validity query [*]
  --stats-internal       print internal (non-public) statistics as well (EXPERTS
                         only) [*]
  --trace=TAG | -t TAG   trace something (e.g. -t pushpop), can repeat and may
                         contain wildcards like (e.g. -t theory::*)

From the Bitvector Theory module:
  --bitblast=MODE        choose bitblasting mode, see --bitblast=help
  --bitwise-eq           lift equivalence with one-bit bit-vectors to be boolean
                         operations [*]
  --bool-to-bv=MODE      convert booleans to bit-vectors of size 1 at various
                         levels of aggressiveness, see --bool-to-bv=help
  --bv-assert-input      assert input assertions on user-level 0 instead of
                         assuming them in the bit-vector SAT solver (EXPERTS
                         only) [*]
  --bv-eager-eval        perform eager context-dependent evaluation for
                         applications of bv kinds in the equality engine [*]
  --bv-gauss-elim        simplify formula via Gaussian Elimination if applicable
                         (EXPERTS only) [*]
  --bv-intro-pow2        introduce bitvector powers of two as a preprocessing
                         pass (EXPERTS only) [*]
  --bv-propagate         use bit-vector propagation in the bit-blaster (EXPERTS
                         only) [*]
  --bv-rw-extend-eq      enable additional rewrites over zero/sign extend over
                         equalities with constants (useful on
                         BV/2017-Preiner-scholl-smt08) (EXPERTS only) [*]
  --bv-sat-solver=MODE   choose which sat solver to use, see
                         --bv-sat-solver=help
  --bv-solver=MODE       choose bit-vector solver, see --bv-solver=help
  --bv-to-bool           lift bit-vectors of size 1 to booleans when possible
                         [*]

From the Datatypes Theory module:
  --cdt-bisimilar        do bisimilarity check for co-datatypes (EXPERTS only)
                         [*]
  --dt-binary-split      do binary splits for datatype constructor types
                         (EXPERTS only) [*]
  --dt-blast-splits      when applicable, blast splitting lemmas for all
                         variables at once (EXPERTS only) [*]
  --dt-cyclic            do cyclicity check for datatypes (EXPERTS only) [*]
  --dt-infer-as-lemmas   always send lemmas out instead of making internal
                         inferences (EXPERTS only) [*]
  --dt-nested-rec        allow nested recursion in datatype definitions (EXPERTS
                         only) [*]
  --dt-polite-optimize   turn on optimization for polite combination (EXPERTS
                         only) [*]
  --dt-share-sel         internally use shared selectors across multiple
                         constructors [*]
  --sygus-abort-size=N   tells enumerative sygus to only consider solutions up
                         to term size N (-1 == no limit, default)
  --sygus-fair=MODE      if and how to apply fairness for sygus
  --sygus-fair-max       use max instead of sum for multi-function sygus
                         conjectures (EXPERTS only) [*]
  --sygus-rewriter=MODE  if and how to apply rewriting for sygus symmetry
                         breaking
  --sygus-simple-sym-break=MODE
                         if and how to apply simple symmetry breaking based on
                         the grammar for smart enumeration
  --sygus-sym-break-lazy lazily add symmetry breaking lemmas for terms (EXPERTS
                         only) [*]
  --sygus-sym-break-pbe  sygus symmetry breaking lemmas based on pbe conjectures
                         [*]
  --sygus-sym-break-rlv  add relevancy conditions to symmetry breaking lemmas
                         (EXPERTS only) [*]

From the Decision Heuristics module:
  --decision=MODE | --decision-mode=MODE
                         choose decision mode, see --decision=help
  --jh-rlv-order         maintain activity-based ordering for decision
                         justification heuristic (EXPERTS only) [*]
  --jh-skolem=MODE       policy for when to satisfy skolem definitions in
                         justification heuristic (EXPERTS only)
  --jh-skolem-rlv=MODE   policy for when to consider skolem definitions relevant
                         in justification heuristic (EXPERTS only)

From the Expression module:
  --type-checking        type check expressions (EXPERTS only) [*]
  --wf-checking          check that terms passed to API methods are well formed
                         (default false for text interface) (EXPERTS only) [*]

From the Finite Field Theory module:
  --ff-field-polys       include field polynomials in Groebner basis
                         computation; don't do this (EXPERTS only) [*]
  --ff-trace-gb          use a traced groebner basis engine (EXPERTS only) [*]

From the Floating-Point module:
  --fp-exp               Allow floating-point sorts of all sizes, rather than
                         only Float32 (8/24) or Float64 (11/53) (experimental)
                         (EXPERTS only) [*]
  --fp-lazy-wb           Enable lazier word-blasting (on preNotifyFact instead
                         of registerTerm) (EXPERTS only) [*]

From the Driver module:
  --dump-difficulty      dump the difficulty measure after every response to
                         check-sat [*]
  --dump-instantiations  output instantiations of quantified formulas after
                         every UNSAT/VALID response [*]
  --dump-instantiations-debug
                         output instantiations of quantified formulas after
                         every UNSAT/VALID response, with debug information
                         (EXPERTS only) [*]
  --dump-models          output models after every SAT/INVALID/UNKNOWN response
                         [*]
  --dump-proofs          output proofs after every UNSAT/VALID response [*]
  --dump-unsat-cores     output unsat cores after every UNSAT/VALID response [*]
  --early-exit           do not run destructors at exit; default on except in
                         debug builds (EXPERTS only) [*]
  --force-no-limit-cpu-while-dump
                         Force no CPU limit when dumping models and proofs
                         (EXPERTS only) [*]
  --portfolio-jobs=n     Number of parallel jobs the portfolio engine can run
                         (EXPERTS only)
  --segv-spin            spin on segfault/other crash waiting for gdb (EXPERTS
                         only) [*]
  --show-trace-tags      show all available tags for tracing (EXPERTS only)
  --stdin-input-per-line when piping from stdin, feed the input to the parser
                         one line at a time. This avoids potential
                         nontermination in the Flex lexer due to not enabling
                         its interactive setting. (EXPERTS only) [*]
  --use-portfolio        Use internal portfolio mode based on the logic (EXPERTS
                         only) [*]

From the Parallel module:
  --append-learned-literals-to-cubes
                         emit learned literals with the cubes (EXPERTS only) [*]
  --checks-before-partition=N
                         number of standard or full effort checks until
                         partitioning (EXPERTS only)
  --checks-between-partitions=N
                         number of checks between partitions (EXPERTS only)
  --compute-partitions=N make n partitions. n <2 disables computing partitions
                         entirely (EXPERTS only)
  --partition-check=MODE | --check=MODE
                         select whether partitioning happens at full or standard
                         check (EXPERTS only)
  --partition-conflict-size=N
                         number of literals in a cube; if no partition size is
                         set, then the partition conflict size is chosen to be
                         log2(number of requested partitions) (EXPERTS only)
  --partition-strategy=MODE | --partition=MODE
                         choose partition strategy mode (EXPERTS only)
  --write-partitions-to=output | --partitions-out=output
                         set the output channel for writing partitions (EXPERTS
                         only)

From the Parser module:
  --filesystem-access    limits the file system access if set to false (EXPERTS
                         only) [*]
  --flex-parser          use flex parser (EXPERTS only) [*]
  --global-declarations  force all declarations and definitions to be global [*]
  --semantic-checks      enable semantic checks, including type checks (EXPERTS
                         only) [*]

From the Printing module:
  --bv-print-consts-as-indexed-symbols
                         print bit-vector constants in decimal (e.g. (_ bv1 4))
                         instead of binary (e.g. #b0001), applies to SMT-LIB 2.x
                         [*]
  --expr-depth=N         print exprs to depth N (0 == default, -1 == no limit)
                         (EXPERTS only)
  --flatten-ho-chains    print (binary) application chains in a flattened way,
                         e.g. (a b c) rather than ((a b) c) (EXPERTS only) [*]
  --model-u-print=MODE   determines how to print uninterpreted elements in
                         models

From the Proof module:
  --check-proof-steps    Check proof steps for satisfiability, for refutation
                         soundness testing. Note this checks only steps for
                         non-core proof rules (EXPERTS only) [*]
  --lfsc-expand-trust    Print the children of trusted proof steps (EXPERTS
                         only) [*]
  --lfsc-flatten         Flatten steps in the LFSC proof (EXPERTS only) [*]
  --opt-res-reconstruction-size
                         Optimize resolution reconstruction to reduce proof size
                         [*]
  --print-dot-clusters   Whether the proof node clusters (e.g. SAT, CNF, INPUT)
                         will be printed when using the dot format or not. [*]
  --proof-alethe-res-pivots
                         Add pivots to Alethe resolution steps (EXPERTS only)
                         [*]
  --proof-annotate       add optional annotations to proofs, which enables
                         statistics for inference ids for lemmas and conflicts
                         appearing in final proof (EXPERTS only) [*]
  --proof-check=MODE     select internal proof checking mode (EXPERTS only)
  --proof-dot-dag        Indicates if the dot proof will be printed as a DAG or
                         as a tree (EXPERTS only) [*]
  --proof-format-mode=MODE
                         select language of proof output
  --proof-granularity=MODE
                         modes for proof granularity
  --proof-pedantic=N     assertion failure for any incorrect rule application or
                         untrusted lemma having pedantic level <=N with proof
                         (EXPERTS only)
  --proof-pp-merge       merge subproofs in final proof post-processor (EXPERTS
                         only) [*]
  --proof-print-conclusion
                         Print conclusion of proof steps when printing AST
                         (EXPERTS only) [*]
  --proof-prune-input    Prune unused input assumptions from final scope
                         (EXPERTS only) [*]
  --proof-rewrite-rcons-limit=N
                         the matching recursion limit for reconstructing proofs
                         of theory rewrites

From the SAT Layer module:
  --minisat-dump-dimacs  instead of solving minisat dumps the asserted clauses
                         in Dimacs format (EXPERTS only) [*]
  --minisat-simplification=MODE
                         Simplifications to be performed by Minisat. (EXPERTS
                         only)
  --preregister-mode=MODE
                         Modes for when to preregister literals. (EXPERTS only)
  --random-freq=P | --random-frequency=P
                         sets the frequency of random decisions in the sat
                         solver (P=0.0 by default) (EXPERTS only)
  --restart-int-base=N   sets the base restart interval for the sat solver (N=25
                         by default) (EXPERTS only)
  --restart-int-inc=F    sets the restart interval increase factor for the sat
                         solver (F=3.0 by default) (EXPERTS only)
  --sat-random-seed=N    sets the random seed for the sat solver

From the Quantifiers module:
  --cbqi                 enable conflict-based quantifier instantiation [*]
  --cbqi-all-conflict    add all available conflicting instances during
                         conflict-based instantiation [*]
  --cbqi-eager-check-rd  optimization, eagerly check relevant domain of matched
                         position (EXPERTS only) [*]
  --cbqi-eager-test      optimization, test cbqi instances eagerly (EXPERTS
                         only) [*]
  --cbqi-mode=MODE       what effort to apply conflict find mechanism
  --cbqi-skip-rd         optimization, skip instances based on possibly
                         irrelevant portions of quantified formulas (EXPERTS
                         only) [*]
  --cbqi-tconstraint     enable entailment checks for t-constraints in cbqi
                         algorithm (EXPERTS only) [*]
  --cbqi-vo-exp          cbqi experimental variable ordering (EXPERTS only) [*]
  --cegis-sample=MODE    mode for using samples in the counterexample-guided
                         inductive synthesis loop
  --cegqi                turns on counterexample-based quantifier instantiation
                         [*]
  --cegqi-all            apply counterexample-based instantiation to all
                         quantified formulas (EXPERTS only) [*]
  --cegqi-bv             use word-level inversion approach for
                         counterexample-guided quantifier instantiation for
                         bit-vectors [*]
  --cegqi-bv-concat-inv  compute inverse for concat over equalities rather than
                         producing an invertibility condition (EXPERTS only) [*]
  --cegqi-bv-ineq=MODE   choose mode for handling bit-vector inequalities with
                         counterexample-guided instantiation
  --cegqi-bv-interleave-value
                         interleave model value instantiation with word-level
                         inversion approach (EXPERTS only) [*]
  --cegqi-bv-linear      linearize adder chains for variables (EXPERTS only) [*]
  --cegqi-bv-rm-extract  replaces extract terms with variables for
                         counterexample-guided instantiation for bit-vectors
                         (EXPERTS only) [*]
  --cegqi-bv-solve-nl    try to solve non-linear bv literals using model value
                         projections (EXPERTS only) [*]
  --cegqi-full           turns on full effort counterexample-based quantifier
                         instantiation, which may resort to model-value
                         instantiation (EXPERTS only) [*]
  --cegqi-inf-int        use integer infinity for vts in counterexample-based
                         quantifier instantiation [*]
  --cegqi-inf-real       use real infinity for vts in counterexample-based
                         quantifier instantiation [*]
  --cegqi-innermost      only process innermost quantified formulas in
                         counterexample-based quantifier instantiation [*]
  --cegqi-midpoint       choose substitutions based on midpoints of lower and
                         upper bounds for counterexample-based quantifier
                         instantiation [*]
  --cegqi-min-bounds     use minimally constrained lower/upper bound for
                         counterexample-based quantifier instantiation (EXPERTS
                         only) [*]
  --cegqi-multi-inst     when applicable, do multi instantiations per quantifier
                         per round in counterexample-based quantifier
                         instantiation (EXPERTS only) [*]
  --cegqi-nested-qe      process nested quantified formulas with quantifier
                         elimination in counterexample-based quantifier
                         instantiation [*]
  --cegqi-nopt           non-optimal bounds for counterexample-based quantifier
                         instantiation (EXPERTS only) [*]
  --cegqi-round-up-lia   round up integer lower bounds in substitutions for
                         counterexample-based quantifier instantiation (EXPERTS
                         only) [*]
  --cond-var-split-quant=MODE
                         split quantified formulas that lead to variable
                         eliminations (EXPERTS only)
  --conjecture-gen       generate candidate conjectures for inductive proofs
                         (EXPERTS only) [*]
  --conjecture-gen-gt-enum=N
                         number of ground terms to generate for model filtering
                         (EXPERTS only)
  --conjecture-gen-max-depth=N
                         maximum depth of terms to consider for conjectures
                         (EXPERTS only)
  --conjecture-gen-per-round=N
                         number of conjectures to generate per instantiation
                         round (EXPERTS only)
  --cons-exp-triggers    use constructor expansion for single constructor
                         datatypes triggers (EXPERTS only) [*]
  --dt-stc-ind           apply strengthening for existential quantification over
                         datatypes based on structural induction (EXPERTS only)
                         [*]
  --dt-var-exp-quant     expand datatype variables bound to one constructor in
                         quantifiers (EXPERTS only) [*]
  --e-matching           whether to do heuristic E-matching [*]
  --elim-taut-quant      eliminate tautological disjuncts of quantified formulas
                         [*]
  --enum-inst            enumerative instantiation: instantiate with ground
                         terms from relevant domain, then arbitrary ground terms
                         before answering unknown [*]
  --enum-inst-interleave interleave enumerative instantiation with other
                         techniques [*]
  --enum-inst-limit=N    maximum number of rounds of enumerative instantiation
                         to apply (-1 means no limit) (EXPERTS only)
  --enum-inst-rd         whether to use relevant domain first for enumerative
                         instantiation strategy (EXPERTS only) [*]
  --enum-inst-stratify   stratify effort levels in enumerative instantiation,
                         which favors speed over fairness (EXPERTS only) [*]
  --enum-inst-sum        enumerating tuples of quantifiers by increasing the sum
                         of indices, rather than the maximum [*]
  --ext-rewrite-quant    apply extended rewriting to bodies of quantified
                         formulas [*]
  --finite-model-find    use finite model finding heuristic for quantifier
                         instantiation [*]
  --fmf-bound            finite model finding on bounded quantification [*]
  --fmf-bound-blast      send all instantiations for bounded ranges in a single
                         round (EXPERTS only) [*]
  --fmf-bound-lazy       enforce bounds for bounded quantification lazily via
                         use of proxy variables (EXPERTS only) [*]
  --fmf-fun              find models for recursively defined functions, assumes
                         functions are admissible [*]
  --fmf-fun-rlv          find models for recursively defined functions, assumes
                         functions are admissible, allows empty type when
                         function is irrelevant [*]
  --fmf-mbqi=MODE        choose mode for model-based quantifier instantiation
                         (EXPERTS only)
  --fmf-type-completion-thresh=N
                         the maximum cardinality of an interpreted type for
                         which exhaustive enumeration in finite model finding is
                         attempted
  --full-saturate-quant  resort to full effort techniques instead of answering
                         unknown due to limited quantifier reasoning. Currently
                         enables enumerative instantiation [*]
  --global-negate        do global negation of input formula (EXPERTS only) [*]
  --ho-elim              eagerly eliminate higher-order constraints [*]
  --ho-elim-store-ax     use store axiom during ho-elim [*]
  --ho-matching          do higher-order matching algorithm for triggers with
                         variable operators (EXPERTS only) [*]
  --ho-merge-term-db     merge term indices modulo equality (EXPERTS only) [*]
  --ieval=MODE           mode for using instantiation evaluation
  --increment-triggers   generate additional triggers as needed during search
                         (EXPERTS only) [*]
  --inst-max-level=N     maximum inst level of terms used to instantiate
                         quantified formulas with (-1 == no limit, default)
                         (EXPERTS only)
  --inst-max-rounds=N    maximum number of instantiation rounds (-1 == no limit,
                         default)
  --inst-no-entail       do not consider instances of quantified formulas that
                         are currently entailed [*]
  --inst-when=MODE       when to apply instantiation
  --inst-when-phase=N    instantiation rounds quantifiers takes (>=1) before
                         allowing theory combination to happen (EXPERTS only)
  --int-wf-ind           apply strengthening for integers based on well-founded
                         induction (EXPERTS only) [*]
  --ite-dtt-split-quant  split ites with dt testers as conditions (EXPERTS only)
                         [*]
  --ite-lift-quant=MODE  ite lifting mode for quantified formulas
  --literal-matching=MODE
                         choose literal matching mode (EXPERTS only)
  --macros-quant         perform quantifiers macro expansion [*]
  --macros-quant-mode=MODE
                         mode for quantifiers macro expansion
  --mbqi                 use model-based quantifier instantiation (EXPERTS only)
                         [*]
  --mbqi-interleave      interleave model-based quantifier instantiation with
                         other techniques (EXPERTS only) [*]
  --mbqi-one-inst-per-round
                         only add one instantiation per quantifier per round for
                         mbqi [*]
  --miniscope-quant=MODE miniscope mode for quantified formulas
  --multi-trigger-cache  caching version of multi triggers [*]
  --multi-trigger-linear implementation of multi triggers where maximum number
                         of instantiations is linear wrt number of ground terms
                         [*]
  --multi-trigger-priority
                         only try multi triggers if single triggers give no
                         instantiations [*]
  --multi-trigger-when-single
                         select multi triggers when single triggers exist [*]
  --oracles              Enable interface to external oracles (EXPERTS only) [*]
  --partial-triggers     use triggers that do not contain all free variables
                         (EXPERTS only) [*]
  --pool-inst            pool-based instantiation: instantiate with ground terms
                         occurring in user-specified pools (EXPERTS only) [*]
  --pre-skolem-quant=MODE
                         modes to apply skolemization eagerly to bodies of
                         quantified formulas
  --pre-skolem-quant-nested
                         apply skolemization to nested quantified formulas
                         (EXPERTS only) [*]
  --prenex-quant=MODE    prenex mode for quantified formulas
  --prenex-quant-user    prenex quantified formulas with user patterns [*]
  --print-inst-full      print instantiations for formulas that do not have
                         given identifiers [*]
  --purify-triggers      purify triggers, e.g. f( x+1 ) becomes f( y ), x mapsto
                         y-1 (EXPERTS only) [*]
  --quant-alpha-equiv    infer alpha equivalence between quantified formulas [*]
  --quant-dsplit=MODE    mode for dynamic quantifiers splitting
  --quant-fun-wd         assume that function defined by quantifiers are well
                         defined (EXPERTS only) [*]
  --quant-ind            use all available techniques for inductive reasoning
                         (EXPERTS only) [*]
  --quant-rep-mode=MODE  selection mode for representatives in quantifiers
                         engine (EXPERTS only)
  --register-quant-body-terms
                         consider ground terms within bodies of quantified
                         formulas for matching (EXPERTS only) [*]
  --relational-triggers  choose relational triggers such as x = f(y), x >= f(y)
                         (EXPERTS only) [*]
  --relevant-triggers    prefer triggers that are more relevant based on SInE
                         style analysis [*]
  --sygus                support SyGuS commands [*]
  --sygus-add-const-grammar
                         statically add constants appearing in conjecture to
                         grammars [*]
  --sygus-arg-relevant   static inference techniques for computing whether
                         arguments of functions-to-synthesize are relevant
                         (EXPERTS only) [*]
  --sygus-auto-unfold    enable approach which automatically unfolds transition
                         systems for directly solving invariant synthesis
                         problems (EXPERTS only) [*]
  --sygus-bool-ite-return-const
                         Only use Boolean constants for return values in
                         unification-based function synthesis (EXPERTS only) [*]
  --sygus-core-connective
                         use unsat core analysis to construct Boolean connective
                         to sygus conjectures [*]
  --sygus-crepair-abort  abort if constant repair techniques are not applicable
                         (EXPERTS only) [*]
  --sygus-enum=MODE      mode for sygus enumeration
  --sygus-enum-fast-num-consts=N
                         the branching factor for the number of interpreted
                         constants to consider for each size when using
                         --sygus-enum=fast (EXPERTS only)
  --sygus-enum-random-p=P
                         the parameter of the geometric distribution used to
                         determine the size of terms generated by
                         --sygus-enum=random (EXPERTS only)
  --sygus-eval-unfold=MODE
                         modes for sygus evaluation unfolding
  --sygus-expr-miner-check-timeout=N
                         timeout (in milliseconds) for satisfiability checks in
                         expression miners (EXPERTS only)
  --sygus-filter-sol=MODE
                         mode for filtering sygus solutions (EXPERTS only)
  --sygus-filter-sol-rev compute backwards filtering to compute whether previous
                         solutions are filtered based on later ones (EXPERTS
                         only) [*]
  --sygus-grammar-cons=MODE
                         mode for SyGuS grammar construction
  --sygus-grammar-norm   statically normalize sygus grammars based on flattening
                         (linearization) (EXPERTS only) [*]
  --sygus-inference      attempt to preprocess arbitrary inputs to sygus
                         conjectures (EXPERTS only) [*]
  --sygus-inst           Enable SyGuS instantiation quantifiers module [*]
  --sygus-inst-mode=MODE select instantiation lemma mode (EXPERTS only)
  --sygus-inst-scope=MODE
                         select scope of ground terms (EXPERTS only)
  --sygus-inst-term-sel=MODE
                         granularity for ground terms (EXPERTS only)
  --sygus-inv-templ=MODE template mode for sygus invariant synthesis (weaken
                         pre-condition, strengthen post-condition, or none)
  --sygus-inv-templ-when-sg
                         use invariant templates (with solution reconstruction)
                         for syntax guided problems (EXPERTS only) [*]
  --sygus-min-grammar    statically minimize sygus grammars [*]
  --sygus-out=MODE       output mode for sygus
  --sygus-pbe            enable approach which unifies conditional solutions,
                         specialized for programming-by-examples (pbe)
                         conjectures [*]
  --sygus-pbe-multi-fair when using multiple enumerators, ensure that we only
                         register value of minimial term size (EXPERTS only) [*]
  --sygus-pbe-multi-fair-diff=N
                         when using multiple enumerators, ensure that we only
                         register values of minimial term size plus this value
                         (default 0) (EXPERTS only)
  --sygus-qe-preproc     use quantifier elimination as a preprocessing step for
                         sygus (EXPERTS only) [*]
  --sygus-query-gen=MODE mode for generating interesting satisfiability queries
                         using SyGuS, for internal fuzzing (EXPERTS only)
  --sygus-query-gen-dump-files=MODE
                         mode for dumping external files corresponding to
                         interesting satisfiability queries with sygus-query-gen
                         (EXPERTS only)
  --sygus-query-gen-thresh=N
                         number of points that we allow to be equal for
                         enumerating satisfiable queries with sygus-query-gen
                         (EXPERTS only)
  --sygus-rec-fun        enable efficient support for recursive functions in
                         sygus grammars (EXPERTS only) [*]
  --sygus-rec-fun-eval-limit=N
                         use a hard limit for how many times in a given
                         evaluator call a recursive function can be evaluated
                         (so infinite loops can be avoided) (EXPERTS only)
  --sygus-repair-const   use approach to repair constants in sygus candidate
                         solutions [*]
  --sygus-repair-const-timeout=N
                         timeout (in milliseconds) for the satisfiability check
                         to repair constants in sygus candidate solutions
                         (EXPERTS only)
  --sygus-rr-synth       use sygus to enumerate candidate rewrite rules (EXPERTS
                         only) [*]
  --sygus-rr-synth-accel add dynamic symmetry breaking clauses based on
                         candidate rewrites (EXPERTS only) [*]
  --sygus-rr-synth-check use satisfiability check to verify correctness of
                         candidate rewrites (EXPERTS only) [*]
  --sygus-rr-synth-filter-cong
                         filter candidate rewrites based on congruence (EXPERTS
                         only) [*]
  --sygus-rr-synth-filter-match
                         filter candidate rewrites based on matching (EXPERTS
                         only) [*]
  --sygus-rr-synth-filter-nl
                         filter non-linear candidate rewrites (EXPERTS only) [*]
  --sygus-rr-synth-filter-order
                         filter candidate rewrites based on variable ordering
                         (EXPERTS only) [*]
  --sygus-rr-synth-input synthesize rewrite rules based on the input formula
                         (EXPERTS only) [*]
  --sygus-rr-synth-input-nvars=N
                         the maximum number of variables per type that appear in
                         rewrites from sygus-rr-synth-input (EXPERTS only)
  --sygus-rr-synth-input-use-bool
                         synthesize Boolean rewrite rules based on the input
                         formula (EXPERTS only) [*]
  --sygus-rr-synth-rec   synthesize rewrite rules over all sygus grammar types
                         recursively (EXPERTS only) [*]
  --sygus-rr-verify      use sygus to verify the correctness of rewrite rules
                         via sampling (EXPERTS only) [*]
  --sygus-sample-fp-uniform
                         sample floating-point values uniformly instead of in a
                         biased fashion (EXPERTS only) [*]
  --sygus-sample-grammar when applicable, use grammar for choosing sample points
                         (EXPERTS only) [*]
  --sygus-samples=N      number of points to consider when doing sygus rewriter
                         sample testing (EXPERTS only)
  --sygus-si=MODE        mode for processing single invocation synthesis
                         conjectures
  --sygus-si-abort       abort if synthesis conjecture is not single invocation
                         [*]
  --sygus-si-rcons=MODE  policy for reconstructing solutions for single
                         invocation conjectures
  --sygus-si-rcons-limit=N
                         number of rounds of enumeration to use during solution
                         reconstruction (negative means unlimited) (EXPERTS
                         only)
  --sygus-stream         enumerate a stream of solutions instead of terminating
                         after the first one [*]
  --sygus-unif-cond-independent-no-repeat-sol
                         Do not try repeated solutions when using independent
                         synthesis of conditions in unification-based function
                         synthesis (EXPERTS only) [*]
  --sygus-unif-pi=MODE   mode for synthesis via piecewise-indepedent unification
  --sygus-unif-shuffle-cond
                         Shuffle condition pool when building solutions (may
                         change solutions sizes) (EXPERTS only) [*]
  --sygus-verify-inst-max-rounds=N
                         maximum number of instantiation rounds for sygus
                         verification calls (-1 == no limit, default is 10)
                         (EXPERTS only)
  --sygus-verify-timeout=N
                         timeout (in milliseconds) for verifying satisfiability
                         of synthesized terms
  --term-db-cd           register terms in term database based on the SAT
                         context (EXPERTS only) [*]
  --term-db-mode=MODE    which ground terms to consider for instantiation
  --trigger-active-sel=MODE
                         selection mode to activate triggers (EXPERTS only)
  --trigger-sel=MODE     selection mode for triggers
  --user-pat=MODE        policy for handling user-provided patterns for
                         quantifier instantiation
  --user-pool=MODE       policy for handling user-provided pools for quantifier
                         instantiation (EXPERTS only)
  --var-elim-quant       enable simple variable elimination for quantified
                         formulas [*]
  --var-ineq-elim-quant  enable variable elimination based on infinite
                         projection of unbound arithmetic variables [*]

From the Separation Logic Theory module:
  --sep-min-refine       only add refinement lemmas for minimal (innermost)
                         assertions (EXPERTS only) [*]
  --sep-pre-skolem-emp   eliminate emp constraint at preprocess time (EXPERTS
                         only) [*]

From the Sets Theory module:
  --sets-ext             enable extended symbols such as complement and universe
                         in theory of sets [*]
  --sets-infer-as-lemmas send inferences as lemmas (EXPERTS only) [*]
  --sets-proxy-lemmas    introduce proxy variables eagerly to shorten lemmas
                         (EXPERTS only) [*]

From the SMT Layer module:
  --abstract-values      in models, output arrays (and in future, maybe others)
                         using abstract values, as required by the SMT-LIB
                         standard (EXPERTS only) [*]
  --ackermann            eliminate functions by ackermannization [*]
  --bvand-integer-granularity=N
                         granularity to use in --solve-bv-as-int mode and for
                         iand operator (experimental) (EXPERTS only)
  --check-abducts        checks whether produced solutions to get-abduct are
                         correct [*]
  --check-interpolants   checks whether produced solutions to get-interpolant
                         are correct [*]
  --check-proofs         after UNSAT/VALID, check the generated proof (with
                         proof) [*]
  --check-synth-sol      checks whether produced solutions to
                         functions-to-synthesize satisfy the conjecture [*]
  --check-unsat-cores    after UNSAT/VALID, produce and check an unsat core
                         (expensive) [*]
  --debug-check-models   after SAT/INVALID/UNKNOWN, check that the generated
                         model satisfies user and internal assertions (EXPERTS
                         only) [*]
  --deep-restart=MODE    mode for deep restarts (EXPERTS only)
  --deep-restart-factor=F
                         sets the threshold for average assertions per literal
                         before a deep restart (EXPERTS only)
  --difficulty-mode=MODE choose output mode for get-difficulty, see
                         --difficulty-mode=help (EXPERTS only)
  --early-ite-removal    remove ITEs early in preprocessing (EXPERTS only) [*]
  --ext-rew-prep=MODE    mode for using extended rewriter as a preprocessing
                         pass, see --ext-rew-prep=help
  --foreign-theory-rewrite
                         Cross-theory rewrites (EXPERTS only) [*]
  --iand-mode=mode       Set the refinement scheme for integer AND (EXPERTS
                         only)
  --interpolants-mode=MODE
                         choose interpolants production mode, see
                         --interpolants-mode=help
  --ite-simp             turn on ite simplification (Kim (and Somenzi) et al.,
                         SAT 2009) (EXPERTS only) [*]
  --learned-rewrite      rewrite the input based on learned literals [*]
  --minimal-unsat-cores  if an unsat core is produced, it is reduced to a
                         minimal unsat core (EXPERTS only) [*]
  --model-cores=MODE     mode for producing model cores
  --model-var-elim-uneval
                         allow variable elimination based on unevaluatable terms
                         to variables (EXPERTS only) [*]
  --on-repeat-ite-simp   do the ite simplification pass again if repeating
                         simplification (EXPERTS only) [*]
  --print-unsat-cores-full
                         when printing unsat cores, include unlabeled assertions
                         [*]
  --produce-abducts      support the get-abduct command [*]
  --produce-assertions | --interactive-mode
                         keep an assertions list. Note this option is always
                         enabled. [*]
  --produce-assignments  support the get-assignment command [*]
  --produce-difficulty   enable tracking of difficulty. [*]
  --produce-interpolants turn on interpolation generation. [*]
  --produce-learned-literals
                         produce learned literals, support get-learned-literals
                         [*]
  --produce-proofs       produce proofs, support check-proofs and get-proof [*]
  --produce-unsat-assumptions
                         turn on unsat assumptions generation [*]
  --produce-unsat-cores  turn on unsat core generation. Unless otherwise
                         specified, cores will be produced using SAT soving
                         under assumptions and preprocessing proofs. [*]
  --proof-mode=MODE      choose proof mode, see --proof-mode=help (EXPERTS only)
  --repeat-simp          make multiple passes with nonclausal simplifier
                         (EXPERTS only) [*]
  --simp-ite-compress    enables compressing ites after ite simplification
                         (EXPERTS only) [*]
  --simp-with-care       enables simplifyWithCare in ite simplificiation
                         (EXPERTS only) [*]
  --simplification=MODE | --simplification-mode=MODE
                         choose simplification mode, see --simplification=help
  --simplification-bcp   apply Boolean constant propagation as a substituion
                         during simplification (EXPERTS only) [*]
  --solve-bv-as-int=MODE mode for translating BVAnd to integer (EXPERTS only)
  --solve-int-as-bv=N    attempt to solve a pure integer satisfiable problem by
                         bitblasting in sufficient bitwidth (experimental)
  --solve-real-as-int    attempt to solve a pure real satisfiable problem as an
                         integer problem (for non-linear) [*]
  --sort-inference       calculate sort inference of input problem, convert the
                         input based on monotonic sorts [*]
  --static-learning      use static learning (on by default) [*]
  --unconstrained-simp   turn on unconstrained simplification (see
                         Bruttomesso/Brummayer PhD thesis). Fully supported only
                         in (subsets of) the logic QF_ABV. [*]
  --unsat-cores-mode=MODE
                         choose unsat core mode, see --unsat-cores-mode=help
                         (EXPERTS only)

From the Strings Theory module:
  --re-elim=MODE         regular expression elimination mode
  --re-inter-mode=MODE   determines which regular expressions intersections to
                         compute (EXPERTS only)
  --seq-array=MODE       use array-inspired solver for sequence updates in eager
                         or lazy mode (EXPERTS only)
  --strings-alpha-card=N the assumed cardinality of the alphabet of characters
                         for strings, which is a prefix of the interval of
                         unicode code points in the SMT-LIB standard (EXPERTS
                         only)
  --strings-check-entail-len
                         check entailment between length terms to reduce
                         splitting [*]
  --strings-code-elim    eliminate code points during preprocessing (EXPERTS
                         only) [*]
  --strings-deq-ext      use extensionality for string disequalities [*]
  --strings-eager-eval   perform eager context-dependent evaluation for
                         applications of string kinds in the equality engine [*]
  --strings-eager-len-re use regular expressions for eager length conflicts [*]
  --strings-eager-reg    do registration lemmas for terms during
                         preregistration. If false, do registration lemmas for
                         terms when they appear in asserted literals (EXPERTS
                         only) [*]
  --strings-eager-solver use the eager solver [*]
  --strings-exp          experimental features in the theory of strings [*]
  --strings-ff           do flat form inferences (EXPERTS only) [*]
  --strings-fmf          the finite model finding used by the theory of strings
                         [*]
  --strings-infer-as-lemmas
                         always send lemmas out instead of making internal
                         inferences (EXPERTS only) [*]
  --strings-infer-sym    generalized inferences in strings based on proxy
                         symbols (EXPERTS only) [*]
  --strings-lazy-pp      perform string preprocessing lazily [*]
  --strings-len-norm     strings length normalization lemma (EXPERTS only) [*]
  --strings-mbr          use models to avoid reductions for extended functions
                         that introduce quantified formulas [*]
  --strings-model-max-len=N
                         The maximum size of string values in models (EXPERTS
                         only)
  --strings-process-loop-mode=MODE
                         determines how to process looping string equations
  --strings-re-posc-eager
                         eager reduction of positive membership into
                         concatentation (EXPERTS only) [*]
  --strings-regexp-inclusion
                         use regular expression inclusion for finding conflicts
                         and avoiding regular expression unfolding [*]
  --strings-rexplain-lemmas
                         regression explanations for string lemmas (EXPERTS
                         only) [*]

From the Theory Layer module:
  --assign-function-values
                         assign values for uninterpreted functions in models
                         (EXPERTS only) [*]
  --condense-function-values
                         condense values for functions in models rather than
                         explicitly representing them (EXPERTS only) [*]
  --ee-mode=MODE         mode for managing equalities across theory solvers
                         (EXPERTS only)
  --relevance-filter     enable analysis of relevance of asserted literals with
                         respect to the input formula (EXPERTS only) [*]
  --tc-mode=MODE         mode for theory combination (EXPERTS only)
  --theoryof-mode=MODE   mode for Theory::theoryof() (EXPERTS only)

From the Uninterpreted Functions Theory module:
  --eager-arith-bv-conv  eagerly expand bit-vector to arithmetic conversions
                         during preprocessing (EXPERTS only) [*]
  --symmetry-breaker     use UF symmetry breaker (Deharbe et al., CADE 2011)
                         (EXPERTS only) [*]
  --uf-ho-ext            apply extensionality on function symbols (EXPERTS only)
                         [*]
  --uf-lazy-ll           do lambda lifting lazily [*]
  --uf-ss=MODE           mode of operation for uf with cardinality solver.
  --uf-ss-abort-card=N   tells the uf with cardinality to only consider models
                         that interpret uninterpreted sorts of cardinality at
                         most N (-1 == no limit, default)
  --uf-ss-fair           use fair strategy for finite model finding multiple
                         sorts [*]
  --uf-ss-fair-monotone  group monotone sorts when enforcing fairness for finite
                         model finding (EXPERTS only) [*]
)FOOBAR";

static const std::string optionsFootnote = "\n\
[*] Each of these options has a --no-OPTIONNAME variant, which reverses the\n\
    sense of the option.\n\
";
// clang-format on

void printUsage(const std::string& binary, std::ostream& os)
{
  os << "usage: " << binary << " [options] [input-file]" << std::endl
     << std::endl
     << "Without an input file, or with `-', cvc5 reads from standard "
        "input."
     << std::endl
     << std::endl
     << "cvc5 options:" << std::endl
     << commonOptionsDescription << std::endl
     << std::endl
     << additionalOptionsDescription << std::endl
     << optionsFootnote << std::endl;
}

/**
 * This is a table of long options.  By policy, each short option
 * should have an equivalent long option (but the reverse isn't the
 * case), so this table should thus contain all command-line options.
 *
 * Each option in this array has four elements:
 *
 * 1. the long option string
 * 2. argument behavior for the option:
 *    no_argument - no argument permitted
 *    required_argument - an argument is expected
 *    optional_argument - an argument is permitted but not required
 * 3. this is a pointer to an int which is set to the 4th entry of the
 *    array if the option is present; or nullptr, in which case
 *    getopt_long() returns the 4th entry
 * 4. the return value for getopt_long() when this long option (or the
 *    value to set the 3rd entry to; see #3)
 */
static struct option cmdlineOptions[] = {
// clang-format off
  { "approx-branch-depth", required_argument, nullptr, 256 },
  { "arith-brab", no_argument, nullptr, 257 },
  { "no-arith-brab", no_argument, nullptr, 258 },
  { "arith-eq-solver", no_argument, nullptr, 259 },
  { "no-arith-eq-solver", no_argument, nullptr, 260 },
  { "arith-no-partial-fun", no_argument, nullptr, 261 },
  { "no-arith-no-partial-fun", no_argument, nullptr, 262 },
  { "arith-prop", required_argument, nullptr, 263 },
  { "arith-prop-clauses", required_argument, nullptr, 264 },
  { "arith-rewrite-equalities", no_argument, nullptr, 265 },
  { "no-arith-rewrite-equalities", no_argument, nullptr, 266 },
  { "arith-static-learning", no_argument, nullptr, 267 },
  { "no-arith-static-learning", no_argument, nullptr, 268 },
  { "collect-pivot-stats", no_argument, nullptr, 269 },
  { "no-collect-pivot-stats", no_argument, nullptr, 270 },
  { "cut-all-bounded", no_argument, nullptr, 271 },
  { "no-cut-all-bounded", no_argument, nullptr, 272 },
  { "dio-decomps", no_argument, nullptr, 273 },
  { "no-dio-decomps", no_argument, nullptr, 274 },
  { "dio-solver", no_argument, nullptr, 275 },
  { "no-dio-solver", no_argument, nullptr, 276 },
  { "dio-turns", required_argument, nullptr, 277 },
  { "error-selection-rule", required_argument, nullptr, 278 },
  { "fc-penalties", no_argument, nullptr, 279 },
  { "no-fc-penalties", no_argument, nullptr, 280 },
  { "heuristic-pivots", required_argument, nullptr, 281 },
  { "lemmas-on-replay-failure", no_argument, nullptr, 282 },
  { "no-lemmas-on-replay-failure", no_argument, nullptr, 283 },
  { "maxCutsInContext", required_argument, nullptr, 284 },
  { "miplib-trick", no_argument, nullptr, 285 },
  { "no-miplib-trick", no_argument, nullptr, 286 },
  { "miplib-trick-subs", required_argument, nullptr, 287 },
  { "new-prop", no_argument, nullptr, 288 },
  { "no-new-prop", no_argument, nullptr, 289 },
  { "nl-cov", no_argument, nullptr, 290 },
  { "no-nl-cov", no_argument, nullptr, 291 },
  { "nl-cov-force", no_argument, nullptr, 292 },
  { "no-nl-cov-force", no_argument, nullptr, 293 },
  { "nl-cov-lift", required_argument, nullptr, 294 },
  { "nl-cov-linear-model", required_argument, nullptr, 295 },
  { "nl-cov-proj", required_argument, nullptr, 296 },
  { "nl-cov-prune", no_argument, nullptr, 297 },
  { "no-nl-cov-prune", no_argument, nullptr, 298 },
  { "nl-cov-var-elim", no_argument, nullptr, 299 },
  { "no-nl-cov-var-elim", no_argument, nullptr, 300 },
  { "nl-ext", required_argument, nullptr, 301 },
  { "nl-ext-ent-conf", no_argument, nullptr, 302 },
  { "no-nl-ext-ent-conf", no_argument, nullptr, 303 },
  { "nl-ext-factor", no_argument, nullptr, 304 },
  { "no-nl-ext-factor", no_argument, nullptr, 305 },
  { "nl-ext-inc-prec", no_argument, nullptr, 306 },
  { "no-nl-ext-inc-prec", no_argument, nullptr, 307 },
  { "nl-ext-purify", no_argument, nullptr, 308 },
  { "no-nl-ext-purify", no_argument, nullptr, 309 },
  { "nl-ext-rbound", no_argument, nullptr, 310 },
  { "no-nl-ext-rbound", no_argument, nullptr, 311 },
  { "nl-ext-rewrite", no_argument, nullptr, 312 },
  { "no-nl-ext-rewrite", no_argument, nullptr, 313 },
  { "nl-ext-split-zero", no_argument, nullptr, 314 },
  { "no-nl-ext-split-zero", no_argument, nullptr, 315 },
  { "nl-ext-tf-taylor-deg", required_argument, nullptr, 316 },
  { "nl-ext-tf-tplanes", no_argument, nullptr, 317 },
  { "no-nl-ext-tf-tplanes", no_argument, nullptr, 318 },
  { "nl-ext-tplanes", no_argument, nullptr, 319 },
  { "no-nl-ext-tplanes", no_argument, nullptr, 320 },
  { "nl-ext-tplanes-interleave", no_argument, nullptr, 321 },
  { "no-nl-ext-tplanes-interleave", no_argument, nullptr, 322 },
  { "nl-icp", no_argument, nullptr, 323 },
  { "no-nl-icp", no_argument, nullptr, 324 },
  { "nl-rlv", required_argument, nullptr, 325 },
  { "nl-rlv-assert-bounds", no_argument, nullptr, 326 },
  { "no-nl-rlv-assert-bounds", no_argument, nullptr, 327 },
  { "pb-rewrites", no_argument, nullptr, 328 },
  { "no-pb-rewrites", no_argument, nullptr, 329 },
  { "pivot-threshold", required_argument, nullptr, 330 },
  { "pp-assert-max-sub-size", required_argument, nullptr, 331 },
  { "prop-row-length", required_argument, nullptr, 332 },
  { "replay-early-close-depth", required_argument, nullptr, 333 },
  { "replay-lemma-reject-cut", required_argument, nullptr, 334 },
  { "replay-num-err-penalty", required_argument, nullptr, 335 },
  { "replay-reject-cut", required_argument, nullptr, 336 },
  { "restrict-pivots", no_argument, nullptr, 337 },
  { "no-restrict-pivots", no_argument, nullptr, 338 },
  { "revert-arith-models-on-unsat", no_argument, nullptr, 339 },
  { "no-revert-arith-models-on-unsat", no_argument, nullptr, 340 },
  { "rr-turns", required_argument, nullptr, 341 },
  { "se-solve-int", no_argument, nullptr, 342 },
  { "no-se-solve-int", no_argument, nullptr, 343 },
  { "simplex-check-period", required_argument, nullptr, 344 },
  { "soi-qe", no_argument, nullptr, 345 },
  { "no-soi-qe", no_argument, nullptr, 346 },
  { "standard-effort-variable-order-pivots", required_argument, nullptr, 347 },
  { "unate-lemmas", required_argument, nullptr, 348 },
  { "use-approx", no_argument, nullptr, 349 },
  { "no-use-approx", no_argument, nullptr, 350 },
  { "use-fcsimplex", no_argument, nullptr, 351 },
  { "no-use-fcsimplex", no_argument, nullptr, 352 },
  { "use-soi", no_argument, nullptr, 353 },
  { "no-use-soi", no_argument, nullptr, 354 },
  { "arrays-eager-index", no_argument, nullptr, 355 },
  { "no-arrays-eager-index", no_argument, nullptr, 356 },
  { "arrays-eager-lemmas", no_argument, nullptr, 357 },
  { "no-arrays-eager-lemmas", no_argument, nullptr, 358 },
  { "arrays-exp", no_argument, nullptr, 359 },
  { "no-arrays-exp", no_argument, nullptr, 360 },
  { "arrays-optimize-linear", no_argument, nullptr, 361 },
  { "no-arrays-optimize-linear", no_argument, nullptr, 362 },
  { "arrays-prop", required_argument, nullptr, 363 },
  { "arrays-reduce-sharing", no_argument, nullptr, 364 },
  { "no-arrays-reduce-sharing", no_argument, nullptr, 365 },
  { "arrays-weak-equiv", no_argument, nullptr, 366 },
  { "no-arrays-weak-equiv", no_argument, nullptr, 367 },
  { "err", required_argument, nullptr, 368 },
  { "diagnostic-output-channel", required_argument, nullptr, 369 },
  { "in", required_argument, nullptr, 370 },
  { "incremental", no_argument, nullptr, 371 },
  { "no-incremental", no_argument, nullptr, 372 },
  { "lang", required_argument, nullptr, 373 },
  { "input-language", required_argument, nullptr, 374 },
  { "out", required_argument, nullptr, 375 },
  { "regular-output-channel", required_argument, nullptr, 376 },
  { "output", required_argument, nullptr, 377 },
  { "parse-only", no_argument, nullptr, 378 },
  { "no-parse-only", no_argument, nullptr, 379 },
  { "preprocess-only", no_argument, nullptr, 380 },
  { "no-preprocess-only", no_argument, nullptr, 381 },
  { "quiet", no_argument, nullptr, 382 },
  { "rlimit", required_argument, nullptr, 383 },
  { "rlimit-per", required_argument, nullptr, 384 },
  { "reproducible-resource-limit", required_argument, nullptr, 385 },
  { "rweight", required_argument, nullptr, 386 },
  { "stats", no_argument, nullptr, 387 },
  { "no-stats", no_argument, nullptr, 388 },
  { "stats-all", no_argument, nullptr, 389 },
  { "no-stats-all", no_argument, nullptr, 390 },
  { "stats-every-query", no_argument, nullptr, 391 },
  { "no-stats-every-query", no_argument, nullptr, 392 },
  { "stats-internal", no_argument, nullptr, 393 },
  { "no-stats-internal", no_argument, nullptr, 394 },
  { "tlimit", required_argument, nullptr, 395 },
  { "tlimit-per", required_argument, nullptr, 396 },
  { "trace", required_argument, nullptr, 397 },
  { "verbose", no_argument, nullptr, 398 },
  { "verbosity", required_argument, nullptr, 399 },
  { "bitblast", required_argument, nullptr, 400 },
  { "bitwise-eq", no_argument, nullptr, 401 },
  { "no-bitwise-eq", no_argument, nullptr, 402 },
  { "bool-to-bv", required_argument, nullptr, 403 },
  { "bv-assert-input", no_argument, nullptr, 404 },
  { "no-bv-assert-input", no_argument, nullptr, 405 },
  { "bv-eager-eval", no_argument, nullptr, 406 },
  { "no-bv-eager-eval", no_argument, nullptr, 407 },
  { "bv-gauss-elim", no_argument, nullptr, 408 },
  { "no-bv-gauss-elim", no_argument, nullptr, 409 },
  { "bv-intro-pow2", no_argument, nullptr, 410 },
  { "no-bv-intro-pow2", no_argument, nullptr, 411 },
  { "bv-propagate", no_argument, nullptr, 412 },
  { "no-bv-propagate", no_argument, nullptr, 413 },
  { "bv-rw-extend-eq", no_argument, nullptr, 414 },
  { "no-bv-rw-extend-eq", no_argument, nullptr, 415 },
  { "bv-sat-solver", required_argument, nullptr, 416 },
  { "bv-solver", required_argument, nullptr, 417 },
  { "bv-to-bool", no_argument, nullptr, 418 },
  { "no-bv-to-bool", no_argument, nullptr, 419 },
  { "cdt-bisimilar", no_argument, nullptr, 420 },
  { "no-cdt-bisimilar", no_argument, nullptr, 421 },
  { "dt-binary-split", no_argument, nullptr, 422 },
  { "no-dt-binary-split", no_argument, nullptr, 423 },
  { "dt-blast-splits", no_argument, nullptr, 424 },
  { "no-dt-blast-splits", no_argument, nullptr, 425 },
  { "dt-cyclic", no_argument, nullptr, 426 },
  { "no-dt-cyclic", no_argument, nullptr, 427 },
  { "dt-infer-as-lemmas", no_argument, nullptr, 428 },
  { "no-dt-infer-as-lemmas", no_argument, nullptr, 429 },
  { "dt-nested-rec", no_argument, nullptr, 430 },
  { "no-dt-nested-rec", no_argument, nullptr, 431 },
  { "dt-polite-optimize", no_argument, nullptr, 432 },
  { "no-dt-polite-optimize", no_argument, nullptr, 433 },
  { "dt-share-sel", no_argument, nullptr, 434 },
  { "no-dt-share-sel", no_argument, nullptr, 435 },
  { "sygus-abort-size", required_argument, nullptr, 436 },
  { "sygus-fair", required_argument, nullptr, 437 },
  { "sygus-fair-max", no_argument, nullptr, 438 },
  { "no-sygus-fair-max", no_argument, nullptr, 439 },
  { "sygus-rewriter", required_argument, nullptr, 440 },
  { "sygus-simple-sym-break", required_argument, nullptr, 441 },
  { "sygus-sym-break-lazy", no_argument, nullptr, 442 },
  { "no-sygus-sym-break-lazy", no_argument, nullptr, 443 },
  { "sygus-sym-break-pbe", no_argument, nullptr, 444 },
  { "no-sygus-sym-break-pbe", no_argument, nullptr, 445 },
  { "sygus-sym-break-rlv", no_argument, nullptr, 446 },
  { "no-sygus-sym-break-rlv", no_argument, nullptr, 447 },
  { "decision", required_argument, nullptr, 448 },
  { "decision-mode", required_argument, nullptr, 449 },
  { "jh-rlv-order", no_argument, nullptr, 450 },
  { "no-jh-rlv-order", no_argument, nullptr, 451 },
  { "jh-skolem", required_argument, nullptr, 452 },
  { "jh-skolem-rlv", required_argument, nullptr, 453 },
  { "type-checking", no_argument, nullptr, 454 },
  { "no-type-checking", no_argument, nullptr, 455 },
  { "wf-checking", no_argument, nullptr, 456 },
  { "no-wf-checking", no_argument, nullptr, 457 },
  { "ff-field-polys", no_argument, nullptr, 458 },
  { "no-ff-field-polys", no_argument, nullptr, 459 },
  { "ff-trace-gb", no_argument, nullptr, 460 },
  { "no-ff-trace-gb", no_argument, nullptr, 461 },
  { "fp-exp", no_argument, nullptr, 462 },
  { "no-fp-exp", no_argument, nullptr, 463 },
  { "fp-lazy-wb", no_argument, nullptr, 464 },
  { "no-fp-lazy-wb", no_argument, nullptr, 465 },
  { "copyright", no_argument, nullptr, 466 },
  { "dump-difficulty", no_argument, nullptr, 467 },
  { "no-dump-difficulty", no_argument, nullptr, 468 },
  { "dump-instantiations", no_argument, nullptr, 469 },
  { "no-dump-instantiations", no_argument, nullptr, 470 },
  { "dump-instantiations-debug", no_argument, nullptr, 471 },
  { "no-dump-instantiations-debug", no_argument, nullptr, 472 },
  { "dump-models", no_argument, nullptr, 473 },
  { "no-dump-models", no_argument, nullptr, 474 },
  { "dump-proofs", no_argument, nullptr, 475 },
  { "no-dump-proofs", no_argument, nullptr, 476 },
  { "dump-unsat-cores", no_argument, nullptr, 477 },
  { "no-dump-unsat-cores", no_argument, nullptr, 478 },
  { "early-exit", no_argument, nullptr, 479 },
  { "no-early-exit", no_argument, nullptr, 480 },
  { "filename", required_argument, nullptr, 481 },
  { "force-no-limit-cpu-while-dump", no_argument, nullptr, 482 },
  { "no-force-no-limit-cpu-while-dump", no_argument, nullptr, 483 },
  { "help", no_argument, nullptr, 484 },
  { "interactive", no_argument, nullptr, 485 },
  { "no-interactive", no_argument, nullptr, 486 },
  { "portfolio-jobs", required_argument, nullptr, 487 },
  { "print-success", no_argument, nullptr, 488 },
  { "no-print-success", no_argument, nullptr, 489 },
  { "seed", required_argument, nullptr, 490 },
  { "segv-spin", no_argument, nullptr, 491 },
  { "no-segv-spin", no_argument, nullptr, 492 },
  { "show-config", no_argument, nullptr, 493 },
  { "show-trace-tags", no_argument, nullptr, 494 },
  { "stdin-input-per-line", no_argument, nullptr, 495 },
  { "no-stdin-input-per-line", no_argument, nullptr, 496 },
  { "use-portfolio", no_argument, nullptr, 497 },
  { "no-use-portfolio", no_argument, nullptr, 498 },
  { "version", no_argument, nullptr, 499 },
  { "append-learned-literals-to-cubes", no_argument, nullptr, 500 },
  { "no-append-learned-literals-to-cubes", no_argument, nullptr, 501 },
  { "checks-before-partition", required_argument, nullptr, 502 },
  { "checks-between-partitions", required_argument, nullptr, 503 },
  { "compute-partitions", required_argument, nullptr, 504 },
  { "partition-check", required_argument, nullptr, 505 },
  { "check", required_argument, nullptr, 506 },
  { "partition-conflict-size", required_argument, nullptr, 507 },
  { "partition-strategy", required_argument, nullptr, 508 },
  { "partition", required_argument, nullptr, 509 },
  { "write-partitions-to", required_argument, nullptr, 510 },
  { "partitions-out", required_argument, nullptr, 511 },
  { "filesystem-access", no_argument, nullptr, 512 },
  { "no-filesystem-access", no_argument, nullptr, 513 },
  { "flex-parser", no_argument, nullptr, 514 },
  { "no-flex-parser", no_argument, nullptr, 515 },
  { "force-logic", required_argument, nullptr, 516 },
  { "global-declarations", no_argument, nullptr, 517 },
  { "no-global-declarations", no_argument, nullptr, 518 },
  { "semantic-checks", no_argument, nullptr, 519 },
  { "no-semantic-checks", no_argument, nullptr, 520 },
  { "strict-parsing", no_argument, nullptr, 521 },
  { "no-strict-parsing", no_argument, nullptr, 522 },
  { "bv-print-consts-as-indexed-symbols", no_argument, nullptr, 523 },
  { "no-bv-print-consts-as-indexed-symbols", no_argument, nullptr, 524 },
  { "dag-thresh", required_argument, nullptr, 525 },
  { "expr-depth", required_argument, nullptr, 526 },
  { "flatten-ho-chains", no_argument, nullptr, 527 },
  { "no-flatten-ho-chains", no_argument, nullptr, 528 },
  { "model-u-print", required_argument, nullptr, 529 },
  { "output-lang", required_argument, nullptr, 530 },
  { "output-language", required_argument, nullptr, 531 },
  { "check-proof-steps", no_argument, nullptr, 532 },
  { "no-check-proof-steps", no_argument, nullptr, 533 },
  { "lfsc-expand-trust", no_argument, nullptr, 534 },
  { "no-lfsc-expand-trust", no_argument, nullptr, 535 },
  { "lfsc-flatten", no_argument, nullptr, 536 },
  { "no-lfsc-flatten", no_argument, nullptr, 537 },
  { "opt-res-reconstruction-size", no_argument, nullptr, 538 },
  { "no-opt-res-reconstruction-size", no_argument, nullptr, 539 },
  { "print-dot-clusters", no_argument, nullptr, 540 },
  { "no-print-dot-clusters", no_argument, nullptr, 541 },
  { "proof-alethe-res-pivots", no_argument, nullptr, 542 },
  { "no-proof-alethe-res-pivots", no_argument, nullptr, 543 },
  { "proof-annotate", no_argument, nullptr, 544 },
  { "no-proof-annotate", no_argument, nullptr, 545 },
  { "proof-check", required_argument, nullptr, 546 },
  { "proof-dot-dag", no_argument, nullptr, 547 },
  { "no-proof-dot-dag", no_argument, nullptr, 548 },
  { "proof-format-mode", required_argument, nullptr, 549 },
  { "proof-granularity", required_argument, nullptr, 550 },
  { "proof-pedantic", required_argument, nullptr, 551 },
  { "proof-pp-merge", no_argument, nullptr, 552 },
  { "no-proof-pp-merge", no_argument, nullptr, 553 },
  { "proof-print-conclusion", no_argument, nullptr, 554 },
  { "no-proof-print-conclusion", no_argument, nullptr, 555 },
  { "proof-prune-input", no_argument, nullptr, 556 },
  { "no-proof-prune-input", no_argument, nullptr, 557 },
  { "proof-rewrite-rcons-limit", required_argument, nullptr, 558 },
  { "minisat-dump-dimacs", no_argument, nullptr, 559 },
  { "no-minisat-dump-dimacs", no_argument, nullptr, 560 },
  { "minisat-simplification", required_argument, nullptr, 561 },
  { "preregister-mode", required_argument, nullptr, 562 },
  { "random-freq", required_argument, nullptr, 563 },
  { "random-frequency", required_argument, nullptr, 564 },
  { "restart-int-base", required_argument, nullptr, 565 },
  { "restart-int-inc", required_argument, nullptr, 566 },
  { "sat-random-seed", required_argument, nullptr, 567 },
  { "cbqi", no_argument, nullptr, 568 },
  { "no-cbqi", no_argument, nullptr, 569 },
  { "cbqi-all-conflict", no_argument, nullptr, 570 },
  { "no-cbqi-all-conflict", no_argument, nullptr, 571 },
  { "cbqi-eager-check-rd", no_argument, nullptr, 572 },
  { "no-cbqi-eager-check-rd", no_argument, nullptr, 573 },
  { "cbqi-eager-test", no_argument, nullptr, 574 },
  { "no-cbqi-eager-test", no_argument, nullptr, 575 },
  { "cbqi-mode", required_argument, nullptr, 576 },
  { "cbqi-skip-rd", no_argument, nullptr, 577 },
  { "no-cbqi-skip-rd", no_argument, nullptr, 578 },
  { "cbqi-tconstraint", no_argument, nullptr, 579 },
  { "no-cbqi-tconstraint", no_argument, nullptr, 580 },
  { "cbqi-vo-exp", no_argument, nullptr, 581 },
  { "no-cbqi-vo-exp", no_argument, nullptr, 582 },
  { "cegis-sample", required_argument, nullptr, 583 },
  { "cegqi", no_argument, nullptr, 584 },
  { "no-cegqi", no_argument, nullptr, 585 },
  { "cegqi-all", no_argument, nullptr, 586 },
  { "no-cegqi-all", no_argument, nullptr, 587 },
  { "cegqi-bv", no_argument, nullptr, 588 },
  { "no-cegqi-bv", no_argument, nullptr, 589 },
  { "cegqi-bv-concat-inv", no_argument, nullptr, 590 },
  { "no-cegqi-bv-concat-inv", no_argument, nullptr, 591 },
  { "cegqi-bv-ineq", required_argument, nullptr, 592 },
  { "cegqi-bv-interleave-value", no_argument, nullptr, 593 },
  { "no-cegqi-bv-interleave-value", no_argument, nullptr, 594 },
  { "cegqi-bv-linear", no_argument, nullptr, 595 },
  { "no-cegqi-bv-linear", no_argument, nullptr, 596 },
  { "cegqi-bv-rm-extract", no_argument, nullptr, 597 },
  { "no-cegqi-bv-rm-extract", no_argument, nullptr, 598 },
  { "cegqi-bv-solve-nl", no_argument, nullptr, 599 },
  { "no-cegqi-bv-solve-nl", no_argument, nullptr, 600 },
  { "cegqi-full", no_argument, nullptr, 601 },
  { "no-cegqi-full", no_argument, nullptr, 602 },
  { "cegqi-inf-int", no_argument, nullptr, 603 },
  { "no-cegqi-inf-int", no_argument, nullptr, 604 },
  { "cegqi-inf-real", no_argument, nullptr, 605 },
  { "no-cegqi-inf-real", no_argument, nullptr, 606 },
  { "cegqi-innermost", no_argument, nullptr, 607 },
  { "no-cegqi-innermost", no_argument, nullptr, 608 },
  { "cegqi-midpoint", no_argument, nullptr, 609 },
  { "no-cegqi-midpoint", no_argument, nullptr, 610 },
  { "cegqi-min-bounds", no_argument, nullptr, 611 },
  { "no-cegqi-min-bounds", no_argument, nullptr, 612 },
  { "cegqi-multi-inst", no_argument, nullptr, 613 },
  { "no-cegqi-multi-inst", no_argument, nullptr, 614 },
  { "cegqi-nested-qe", no_argument, nullptr, 615 },
  { "no-cegqi-nested-qe", no_argument, nullptr, 616 },
  { "cegqi-nopt", no_argument, nullptr, 617 },
  { "no-cegqi-nopt", no_argument, nullptr, 618 },
  { "cegqi-round-up-lia", no_argument, nullptr, 619 },
  { "no-cegqi-round-up-lia", no_argument, nullptr, 620 },
  { "cond-var-split-quant", required_argument, nullptr, 621 },
  { "conjecture-gen", no_argument, nullptr, 622 },
  { "no-conjecture-gen", no_argument, nullptr, 623 },
  { "conjecture-gen-gt-enum", required_argument, nullptr, 624 },
  { "conjecture-gen-max-depth", required_argument, nullptr, 625 },
  { "conjecture-gen-per-round", required_argument, nullptr, 626 },
  { "cons-exp-triggers", no_argument, nullptr, 627 },
  { "no-cons-exp-triggers", no_argument, nullptr, 628 },
  { "dt-stc-ind", no_argument, nullptr, 629 },
  { "no-dt-stc-ind", no_argument, nullptr, 630 },
  { "dt-var-exp-quant", no_argument, nullptr, 631 },
  { "no-dt-var-exp-quant", no_argument, nullptr, 632 },
  { "e-matching", no_argument, nullptr, 633 },
  { "no-e-matching", no_argument, nullptr, 634 },
  { "elim-taut-quant", no_argument, nullptr, 635 },
  { "no-elim-taut-quant", no_argument, nullptr, 636 },
  { "enum-inst", no_argument, nullptr, 637 },
  { "no-enum-inst", no_argument, nullptr, 638 },
  { "enum-inst-interleave", no_argument, nullptr, 639 },
  { "no-enum-inst-interleave", no_argument, nullptr, 640 },
  { "enum-inst-limit", required_argument, nullptr, 641 },
  { "enum-inst-rd", no_argument, nullptr, 642 },
  { "no-enum-inst-rd", no_argument, nullptr, 643 },
  { "enum-inst-stratify", no_argument, nullptr, 644 },
  { "no-enum-inst-stratify", no_argument, nullptr, 645 },
  { "enum-inst-sum", no_argument, nullptr, 646 },
  { "no-enum-inst-sum", no_argument, nullptr, 647 },
  { "ext-rewrite-quant", no_argument, nullptr, 648 },
  { "no-ext-rewrite-quant", no_argument, nullptr, 649 },
  { "finite-model-find", no_argument, nullptr, 650 },
  { "no-finite-model-find", no_argument, nullptr, 651 },
  { "fmf-bound", no_argument, nullptr, 652 },
  { "no-fmf-bound", no_argument, nullptr, 653 },
  { "fmf-bound-blast", no_argument, nullptr, 654 },
  { "no-fmf-bound-blast", no_argument, nullptr, 655 },
  { "fmf-bound-lazy", no_argument, nullptr, 656 },
  { "no-fmf-bound-lazy", no_argument, nullptr, 657 },
  { "fmf-fun", no_argument, nullptr, 658 },
  { "no-fmf-fun", no_argument, nullptr, 659 },
  { "fmf-fun-rlv", no_argument, nullptr, 660 },
  { "no-fmf-fun-rlv", no_argument, nullptr, 661 },
  { "fmf-mbqi", required_argument, nullptr, 662 },
  { "fmf-type-completion-thresh", required_argument, nullptr, 663 },
  { "full-saturate-quant", no_argument, nullptr, 664 },
  { "no-full-saturate-quant", no_argument, nullptr, 665 },
  { "global-negate", no_argument, nullptr, 666 },
  { "no-global-negate", no_argument, nullptr, 667 },
  { "ho-elim", no_argument, nullptr, 668 },
  { "no-ho-elim", no_argument, nullptr, 669 },
  { "ho-elim-store-ax", no_argument, nullptr, 670 },
  { "no-ho-elim-store-ax", no_argument, nullptr, 671 },
  { "ho-matching", no_argument, nullptr, 672 },
  { "no-ho-matching", no_argument, nullptr, 673 },
  { "ho-merge-term-db", no_argument, nullptr, 674 },
  { "no-ho-merge-term-db", no_argument, nullptr, 675 },
  { "ieval", required_argument, nullptr, 676 },
  { "increment-triggers", no_argument, nullptr, 677 },
  { "no-increment-triggers", no_argument, nullptr, 678 },
  { "inst-max-level", required_argument, nullptr, 679 },
  { "inst-max-rounds", required_argument, nullptr, 680 },
  { "inst-no-entail", no_argument, nullptr, 681 },
  { "no-inst-no-entail", no_argument, nullptr, 682 },
  { "inst-when", required_argument, nullptr, 683 },
  { "inst-when-phase", required_argument, nullptr, 684 },
  { "int-wf-ind", no_argument, nullptr, 685 },
  { "no-int-wf-ind", no_argument, nullptr, 686 },
  { "ite-dtt-split-quant", no_argument, nullptr, 687 },
  { "no-ite-dtt-split-quant", no_argument, nullptr, 688 },
  { "ite-lift-quant", required_argument, nullptr, 689 },
  { "literal-matching", required_argument, nullptr, 690 },
  { "macros-quant", no_argument, nullptr, 691 },
  { "no-macros-quant", no_argument, nullptr, 692 },
  { "macros-quant-mode", required_argument, nullptr, 693 },
  { "mbqi", no_argument, nullptr, 694 },
  { "no-mbqi", no_argument, nullptr, 695 },
  { "mbqi-interleave", no_argument, nullptr, 696 },
  { "no-mbqi-interleave", no_argument, nullptr, 697 },
  { "mbqi-one-inst-per-round", no_argument, nullptr, 698 },
  { "no-mbqi-one-inst-per-round", no_argument, nullptr, 699 },
  { "miniscope-quant", required_argument, nullptr, 700 },
  { "multi-trigger-cache", no_argument, nullptr, 701 },
  { "no-multi-trigger-cache", no_argument, nullptr, 702 },
  { "multi-trigger-linear", no_argument, nullptr, 703 },
  { "no-multi-trigger-linear", no_argument, nullptr, 704 },
  { "multi-trigger-priority", no_argument, nullptr, 705 },
  { "no-multi-trigger-priority", no_argument, nullptr, 706 },
  { "multi-trigger-when-single", no_argument, nullptr, 707 },
  { "no-multi-trigger-when-single", no_argument, nullptr, 708 },
  { "oracles", no_argument, nullptr, 709 },
  { "no-oracles", no_argument, nullptr, 710 },
  { "partial-triggers", no_argument, nullptr, 711 },
  { "no-partial-triggers", no_argument, nullptr, 712 },
  { "pool-inst", no_argument, nullptr, 713 },
  { "no-pool-inst", no_argument, nullptr, 714 },
  { "pre-skolem-quant", required_argument, nullptr, 715 },
  { "pre-skolem-quant-nested", no_argument, nullptr, 716 },
  { "no-pre-skolem-quant-nested", no_argument, nullptr, 717 },
  { "prenex-quant", required_argument, nullptr, 718 },
  { "prenex-quant-user", no_argument, nullptr, 719 },
  { "no-prenex-quant-user", no_argument, nullptr, 720 },
  { "print-inst", required_argument, nullptr, 721 },
  { "print-inst-full", no_argument, nullptr, 722 },
  { "no-print-inst-full", no_argument, nullptr, 723 },
  { "purify-triggers", no_argument, nullptr, 724 },
  { "no-purify-triggers", no_argument, nullptr, 725 },
  { "quant-alpha-equiv", no_argument, nullptr, 726 },
  { "no-quant-alpha-equiv", no_argument, nullptr, 727 },
  { "quant-dsplit", required_argument, nullptr, 728 },
  { "quant-fun-wd", no_argument, nullptr, 729 },
  { "no-quant-fun-wd", no_argument, nullptr, 730 },
  { "quant-ind", no_argument, nullptr, 731 },
  { "no-quant-ind", no_argument, nullptr, 732 },
  { "quant-rep-mode", required_argument, nullptr, 733 },
  { "register-quant-body-terms", no_argument, nullptr, 734 },
  { "no-register-quant-body-terms", no_argument, nullptr, 735 },
  { "relational-triggers", no_argument, nullptr, 736 },
  { "no-relational-triggers", no_argument, nullptr, 737 },
  { "relevant-triggers", no_argument, nullptr, 738 },
  { "no-relevant-triggers", no_argument, nullptr, 739 },
  { "sygus", no_argument, nullptr, 740 },
  { "no-sygus", no_argument, nullptr, 741 },
  { "sygus-add-const-grammar", no_argument, nullptr, 742 },
  { "no-sygus-add-const-grammar", no_argument, nullptr, 743 },
  { "sygus-arg-relevant", no_argument, nullptr, 744 },
  { "no-sygus-arg-relevant", no_argument, nullptr, 745 },
  { "sygus-auto-unfold", no_argument, nullptr, 746 },
  { "no-sygus-auto-unfold", no_argument, nullptr, 747 },
  { "sygus-bool-ite-return-const", no_argument, nullptr, 748 },
  { "no-sygus-bool-ite-return-const", no_argument, nullptr, 749 },
  { "sygus-core-connective", no_argument, nullptr, 750 },
  { "no-sygus-core-connective", no_argument, nullptr, 751 },
  { "sygus-crepair-abort", no_argument, nullptr, 752 },
  { "no-sygus-crepair-abort", no_argument, nullptr, 753 },
  { "sygus-enum", required_argument, nullptr, 754 },
  { "sygus-enum-fast-num-consts", required_argument, nullptr, 755 },
  { "sygus-enum-random-p", required_argument, nullptr, 756 },
  { "sygus-eval-unfold", required_argument, nullptr, 757 },
  { "sygus-expr-miner-check-timeout", required_argument, nullptr, 758 },
  { "sygus-filter-sol", required_argument, nullptr, 759 },
  { "sygus-filter-sol-rev", no_argument, nullptr, 760 },
  { "no-sygus-filter-sol-rev", no_argument, nullptr, 761 },
  { "sygus-grammar-cons", required_argument, nullptr, 762 },
  { "sygus-grammar-norm", no_argument, nullptr, 763 },
  { "no-sygus-grammar-norm", no_argument, nullptr, 764 },
  { "sygus-inference", no_argument, nullptr, 765 },
  { "no-sygus-inference", no_argument, nullptr, 766 },
  { "sygus-inst", no_argument, nullptr, 767 },
  { "no-sygus-inst", no_argument, nullptr, 768 },
  { "sygus-inst-mode", required_argument, nullptr, 769 },
  { "sygus-inst-scope", required_argument, nullptr, 770 },
  { "sygus-inst-term-sel", required_argument, nullptr, 771 },
  { "sygus-inv-templ", required_argument, nullptr, 772 },
  { "sygus-inv-templ-when-sg", no_argument, nullptr, 773 },
  { "no-sygus-inv-templ-when-sg", no_argument, nullptr, 774 },
  { "sygus-min-grammar", no_argument, nullptr, 775 },
  { "no-sygus-min-grammar", no_argument, nullptr, 776 },
  { "sygus-out", required_argument, nullptr, 777 },
  { "sygus-pbe", no_argument, nullptr, 778 },
  { "no-sygus-pbe", no_argument, nullptr, 779 },
  { "sygus-pbe-multi-fair", no_argument, nullptr, 780 },
  { "no-sygus-pbe-multi-fair", no_argument, nullptr, 781 },
  { "sygus-pbe-multi-fair-diff", required_argument, nullptr, 782 },
  { "sygus-qe-preproc", no_argument, nullptr, 783 },
  { "no-sygus-qe-preproc", no_argument, nullptr, 784 },
  { "sygus-query-gen", required_argument, nullptr, 785 },
  { "sygus-query-gen-dump-files", required_argument, nullptr, 786 },
  { "sygus-query-gen-thresh", required_argument, nullptr, 787 },
  { "sygus-rec-fun", no_argument, nullptr, 788 },
  { "no-sygus-rec-fun", no_argument, nullptr, 789 },
  { "sygus-rec-fun-eval-limit", required_argument, nullptr, 790 },
  { "sygus-repair-const", no_argument, nullptr, 791 },
  { "no-sygus-repair-const", no_argument, nullptr, 792 },
  { "sygus-repair-const-timeout", required_argument, nullptr, 793 },
  { "sygus-rr-synth", no_argument, nullptr, 794 },
  { "no-sygus-rr-synth", no_argument, nullptr, 795 },
  { "sygus-rr-synth-accel", no_argument, nullptr, 796 },
  { "no-sygus-rr-synth-accel", no_argument, nullptr, 797 },
  { "sygus-rr-synth-check", no_argument, nullptr, 798 },
  { "no-sygus-rr-synth-check", no_argument, nullptr, 799 },
  { "sygus-rr-synth-filter-cong", no_argument, nullptr, 800 },
  { "no-sygus-rr-synth-filter-cong", no_argument, nullptr, 801 },
  { "sygus-rr-synth-filter-match", no_argument, nullptr, 802 },
  { "no-sygus-rr-synth-filter-match", no_argument, nullptr, 803 },
  { "sygus-rr-synth-filter-nl", no_argument, nullptr, 804 },
  { "no-sygus-rr-synth-filter-nl", no_argument, nullptr, 805 },
  { "sygus-rr-synth-filter-order", no_argument, nullptr, 806 },
  { "no-sygus-rr-synth-filter-order", no_argument, nullptr, 807 },
  { "sygus-rr-synth-input", no_argument, nullptr, 808 },
  { "no-sygus-rr-synth-input", no_argument, nullptr, 809 },
  { "sygus-rr-synth-input-nvars", required_argument, nullptr, 810 },
  { "sygus-rr-synth-input-use-bool", no_argument, nullptr, 811 },
  { "no-sygus-rr-synth-input-use-bool", no_argument, nullptr, 812 },
  { "sygus-rr-synth-rec", no_argument, nullptr, 813 },
  { "no-sygus-rr-synth-rec", no_argument, nullptr, 814 },
  { "sygus-rr-verify", no_argument, nullptr, 815 },
  { "no-sygus-rr-verify", no_argument, nullptr, 816 },
  { "sygus-sample-fp-uniform", no_argument, nullptr, 817 },
  { "no-sygus-sample-fp-uniform", no_argument, nullptr, 818 },
  { "sygus-sample-grammar", no_argument, nullptr, 819 },
  { "no-sygus-sample-grammar", no_argument, nullptr, 820 },
  { "sygus-samples", required_argument, nullptr, 821 },
  { "sygus-si", required_argument, nullptr, 822 },
  { "sygus-si-abort", no_argument, nullptr, 823 },
  { "no-sygus-si-abort", no_argument, nullptr, 824 },
  { "sygus-si-rcons", required_argument, nullptr, 825 },
  { "sygus-si-rcons-limit", required_argument, nullptr, 826 },
  { "sygus-stream", no_argument, nullptr, 827 },
  { "no-sygus-stream", no_argument, nullptr, 828 },
  { "sygus-unif-cond-independent-no-repeat-sol", no_argument, nullptr, 829 },
  { "no-sygus-unif-cond-independent-no-repeat-sol", no_argument, nullptr, 830 },
  { "sygus-unif-pi", required_argument, nullptr, 831 },
  { "sygus-unif-shuffle-cond", no_argument, nullptr, 832 },
  { "no-sygus-unif-shuffle-cond", no_argument, nullptr, 833 },
  { "sygus-verify-inst-max-rounds", required_argument, nullptr, 834 },
  { "sygus-verify-timeout", required_argument, nullptr, 835 },
  { "term-db-cd", no_argument, nullptr, 836 },
  { "no-term-db-cd", no_argument, nullptr, 837 },
  { "term-db-mode", required_argument, nullptr, 838 },
  { "trigger-active-sel", required_argument, nullptr, 839 },
  { "trigger-sel", required_argument, nullptr, 840 },
  { "user-pat", required_argument, nullptr, 841 },
  { "user-pool", required_argument, nullptr, 842 },
  { "var-elim-quant", no_argument, nullptr, 843 },
  { "no-var-elim-quant", no_argument, nullptr, 844 },
  { "var-ineq-elim-quant", no_argument, nullptr, 845 },
  { "no-var-ineq-elim-quant", no_argument, nullptr, 846 },
  { "sep-min-refine", no_argument, nullptr, 847 },
  { "no-sep-min-refine", no_argument, nullptr, 848 },
  { "sep-pre-skolem-emp", no_argument, nullptr, 849 },
  { "no-sep-pre-skolem-emp", no_argument, nullptr, 850 },
  { "sets-ext", no_argument, nullptr, 851 },
  { "no-sets-ext", no_argument, nullptr, 852 },
  { "sets-infer-as-lemmas", no_argument, nullptr, 853 },
  { "no-sets-infer-as-lemmas", no_argument, nullptr, 854 },
  { "sets-proxy-lemmas", no_argument, nullptr, 855 },
  { "no-sets-proxy-lemmas", no_argument, nullptr, 856 },
  { "abstract-values", no_argument, nullptr, 857 },
  { "no-abstract-values", no_argument, nullptr, 858 },
  { "ackermann", no_argument, nullptr, 859 },
  { "no-ackermann", no_argument, nullptr, 860 },
  { "bv-to-int-use-pow2", no_argument, nullptr, 861 },
  { "no-bv-to-int-use-pow2", no_argument, nullptr, 862 },
  { "bvand-integer-granularity", required_argument, nullptr, 863 },
  { "check-abducts", no_argument, nullptr, 864 },
  { "no-check-abducts", no_argument, nullptr, 865 },
  { "check-interpolants", no_argument, nullptr, 866 },
  { "no-check-interpolants", no_argument, nullptr, 867 },
  { "check-models", no_argument, nullptr, 868 },
  { "no-check-models", no_argument, nullptr, 869 },
  { "check-proofs", no_argument, nullptr, 870 },
  { "no-check-proofs", no_argument, nullptr, 871 },
  { "check-synth-sol", no_argument, nullptr, 872 },
  { "no-check-synth-sol", no_argument, nullptr, 873 },
  { "check-unsat-cores", no_argument, nullptr, 874 },
  { "no-check-unsat-cores", no_argument, nullptr, 875 },
  { "debug-check-models", no_argument, nullptr, 876 },
  { "no-debug-check-models", no_argument, nullptr, 877 },
  { "deep-restart", required_argument, nullptr, 878 },
  { "deep-restart-factor", required_argument, nullptr, 879 },
  { "difficulty-mode", required_argument, nullptr, 880 },
  { "early-ite-removal", no_argument, nullptr, 881 },
  { "no-early-ite-removal", no_argument, nullptr, 882 },
  { "ext-rew-prep", required_argument, nullptr, 883 },
  { "foreign-theory-rewrite", no_argument, nullptr, 884 },
  { "no-foreign-theory-rewrite", no_argument, nullptr, 885 },
  { "iand-mode", required_argument, nullptr, 886 },
  { "interpolants-mode", required_argument, nullptr, 887 },
  { "ite-simp", no_argument, nullptr, 888 },
  { "no-ite-simp", no_argument, nullptr, 889 },
  { "learned-rewrite", no_argument, nullptr, 890 },
  { "no-learned-rewrite", no_argument, nullptr, 891 },
  { "minimal-unsat-cores", no_argument, nullptr, 892 },
  { "no-minimal-unsat-cores", no_argument, nullptr, 893 },
  { "model-cores", required_argument, nullptr, 894 },
  { "model-var-elim-uneval", no_argument, nullptr, 895 },
  { "no-model-var-elim-uneval", no_argument, nullptr, 896 },
  { "on-repeat-ite-simp", no_argument, nullptr, 897 },
  { "no-on-repeat-ite-simp", no_argument, nullptr, 898 },
  { "print-unsat-cores-full", no_argument, nullptr, 899 },
  { "no-print-unsat-cores-full", no_argument, nullptr, 900 },
  { "produce-abducts", no_argument, nullptr, 901 },
  { "no-produce-abducts", no_argument, nullptr, 902 },
  { "produce-assertions", no_argument, nullptr, 903 },
  { "interactive-mode", no_argument, nullptr, 904 },
  { "no-produce-assertions", no_argument, nullptr, 905 },
  { "no-interactive-mode", no_argument, nullptr, 906 },
  { "produce-assignments", no_argument, nullptr, 907 },
  { "no-produce-assignments", no_argument, nullptr, 908 },
  { "produce-difficulty", no_argument, nullptr, 909 },
  { "no-produce-difficulty", no_argument, nullptr, 910 },
  { "produce-interpolants", no_argument, nullptr, 911 },
  { "no-produce-interpolants", no_argument, nullptr, 912 },
  { "produce-learned-literals", no_argument, nullptr, 913 },
  { "no-produce-learned-literals", no_argument, nullptr, 914 },
  { "produce-models", no_argument, nullptr, 915 },
  { "no-produce-models", no_argument, nullptr, 916 },
  { "produce-proofs", no_argument, nullptr, 917 },
  { "no-produce-proofs", no_argument, nullptr, 918 },
  { "produce-unsat-assumptions", no_argument, nullptr, 919 },
  { "no-produce-unsat-assumptions", no_argument, nullptr, 920 },
  { "produce-unsat-cores", no_argument, nullptr, 921 },
  { "no-produce-unsat-cores", no_argument, nullptr, 922 },
  { "proof-mode", required_argument, nullptr, 923 },
  { "repeat-simp", no_argument, nullptr, 924 },
  { "no-repeat-simp", no_argument, nullptr, 925 },
  { "simp-ite-compress", no_argument, nullptr, 926 },
  { "no-simp-ite-compress", no_argument, nullptr, 927 },
  { "simp-with-care", no_argument, nullptr, 928 },
  { "no-simp-with-care", no_argument, nullptr, 929 },
  { "simplification", required_argument, nullptr, 930 },
  { "simplification-mode", required_argument, nullptr, 931 },
  { "simplification-bcp", no_argument, nullptr, 932 },
  { "no-simplification-bcp", no_argument, nullptr, 933 },
  { "solve-bv-as-int", required_argument, nullptr, 934 },
  { "solve-int-as-bv", required_argument, nullptr, 935 },
  { "solve-real-as-int", no_argument, nullptr, 936 },
  { "no-solve-real-as-int", no_argument, nullptr, 937 },
  { "sort-inference", no_argument, nullptr, 938 },
  { "no-sort-inference", no_argument, nullptr, 939 },
  { "static-learning", no_argument, nullptr, 940 },
  { "no-static-learning", no_argument, nullptr, 941 },
  { "unconstrained-simp", no_argument, nullptr, 942 },
  { "no-unconstrained-simp", no_argument, nullptr, 943 },
  { "unsat-cores-mode", required_argument, nullptr, 944 },
  { "re-elim", required_argument, nullptr, 945 },
  { "re-inter-mode", required_argument, nullptr, 946 },
  { "seq-array", required_argument, nullptr, 947 },
  { "strings-alpha-card", required_argument, nullptr, 948 },
  { "strings-check-entail-len", no_argument, nullptr, 949 },
  { "no-strings-check-entail-len", no_argument, nullptr, 950 },
  { "strings-code-elim", no_argument, nullptr, 951 },
  { "no-strings-code-elim", no_argument, nullptr, 952 },
  { "strings-deq-ext", no_argument, nullptr, 953 },
  { "no-strings-deq-ext", no_argument, nullptr, 954 },
  { "strings-eager-eval", no_argument, nullptr, 955 },
  { "no-strings-eager-eval", no_argument, nullptr, 956 },
  { "strings-eager-len-re", no_argument, nullptr, 957 },
  { "no-strings-eager-len-re", no_argument, nullptr, 958 },
  { "strings-eager-reg", no_argument, nullptr, 959 },
  { "no-strings-eager-reg", no_argument, nullptr, 960 },
  { "strings-eager-solver", no_argument, nullptr, 961 },
  { "no-strings-eager-solver", no_argument, nullptr, 962 },
  { "strings-exp", no_argument, nullptr, 963 },
  { "no-strings-exp", no_argument, nullptr, 964 },
  { "strings-ff", no_argument, nullptr, 965 },
  { "no-strings-ff", no_argument, nullptr, 966 },
  { "strings-fmf", no_argument, nullptr, 967 },
  { "no-strings-fmf", no_argument, nullptr, 968 },
  { "strings-infer-as-lemmas", no_argument, nullptr, 969 },
  { "no-strings-infer-as-lemmas", no_argument, nullptr, 970 },
  { "strings-infer-sym", no_argument, nullptr, 971 },
  { "no-strings-infer-sym", no_argument, nullptr, 972 },
  { "strings-lazy-pp", no_argument, nullptr, 973 },
  { "no-strings-lazy-pp", no_argument, nullptr, 974 },
  { "strings-len-norm", no_argument, nullptr, 975 },
  { "no-strings-len-norm", no_argument, nullptr, 976 },
  { "strings-mbr", no_argument, nullptr, 977 },
  { "no-strings-mbr", no_argument, nullptr, 978 },
  { "strings-model-max-len", required_argument, nullptr, 979 },
  { "strings-process-loop-mode", required_argument, nullptr, 980 },
  { "strings-re-posc-eager", no_argument, nullptr, 981 },
  { "no-strings-re-posc-eager", no_argument, nullptr, 982 },
  { "strings-regexp-inclusion", no_argument, nullptr, 983 },
  { "no-strings-regexp-inclusion", no_argument, nullptr, 984 },
  { "strings-rexplain-lemmas", no_argument, nullptr, 985 },
  { "no-strings-rexplain-lemmas", no_argument, nullptr, 986 },
  { "assign-function-values", no_argument, nullptr, 987 },
  { "no-assign-function-values", no_argument, nullptr, 988 },
  { "condense-function-values", no_argument, nullptr, 989 },
  { "no-condense-function-values", no_argument, nullptr, 990 },
  { "ee-mode", required_argument, nullptr, 991 },
  { "relevance-filter", no_argument, nullptr, 992 },
  { "no-relevance-filter", no_argument, nullptr, 993 },
  { "tc-mode", required_argument, nullptr, 994 },
  { "theoryof-mode", required_argument, nullptr, 995 },
  { "eager-arith-bv-conv", no_argument, nullptr, 996 },
  { "no-eager-arith-bv-conv", no_argument, nullptr, 997 },
  { "symmetry-breaker", no_argument, nullptr, 998 },
  { "no-symmetry-breaker", no_argument, nullptr, 999 },
  { "uf-ho-ext", no_argument, nullptr, 1000 },
  { "no-uf-ho-ext", no_argument, nullptr, 1001 },
  { "uf-lazy-ll", no_argument, nullptr, 1002 },
  { "no-uf-lazy-ll", no_argument, nullptr, 1003 },
  { "uf-ss", required_argument, nullptr, 1004 },
  { "uf-ss-abort-card", required_argument, nullptr, 1005 },
  { "uf-ss-fair", no_argument, nullptr, 1006 },
  { "no-uf-ss-fair", no_argument, nullptr, 1007 },
  { "uf-ss-fair-monotone", no_argument, nullptr, 1008 },
  { "no-uf-ss-fair-monotone", no_argument, nullptr, 1009 },
// clang-format on
  {nullptr, no_argument, nullptr, '\0'}
};

std::string suggestCommandLineOptions(const std::string& optionName)
{
  DidYouMean didYouMean;

  const char* opt;
  for (size_t i = 0; (opt = cmdlineOptions[i].name) != nullptr; ++i)
  {
    didYouMean.addWord(std::string("--") + cmdlineOptions[i].name);
  }

  return didYouMean.getMatchAsString(
      optionName.substr(0, optionName.find('=')));
}

void parseInternal(cvc5::Solver& solver,
                   int argc,
                   char* argv[],
                   std::vector<std::string>& nonoptions)
{
  Assert(argv != nullptr);
  if (TraceIsOn("options"))
  {
    Trace("options") << "starting a new parseInternal with " << argc
                     << " arguments" << std::endl;
    for (int i = 0; i < argc; ++i)
    {
      Assert(argv[i] != nullptr);
      Trace("options") << "  argv[" << i << "] = " << argv[i] << std::endl;
    }
  }

  // Reset getopt(), in the case of multiple calls to parse().
  // This can be = 1 in newer GNU getopt, but older (< 2007) require = 0.
  optind = 0;
#if HAVE_DECL_OPTRESET
  optreset = 1; // on BSD getopt() (e.g. Mac OS), might need this
#endif /* HAVE_DECL_OPTRESET */

  // We must parse the binary name, which is manually ignored below. Setting
  // this to 1 leads to incorrect behavior on some platforms.
  int main_optind = 0;
  int old_optind;

  while (true)
  {  // Repeat Forever

    optopt = 0;

    optind = main_optind;
    old_optind = main_optind;

    // If we encounter an element that is not at zero and does not start
    // with a "-", this is a non-option. We consume this element as a
    // non-option.
    if (main_optind > 0 && main_optind < argc && argv[main_optind][0] != '-')
    {
      Trace("options") << "enqueueing " << argv[main_optind]
                       << " as a non-option." << std::endl;
      nonoptions.push_back(argv[main_optind]);
      ++main_optind;
      continue;
    }

    Trace("options") << "[ before, main_optind == " << main_optind << " ]"
                     << std::endl;
    Trace("options") << "[ before, optind == " << optind << " ]" << std::endl;
    Trace("options") << "[ argc == " << argc << ", argv == " << argv << " ]"
                     << std::endl;
    // clang-format off
    int c = getopt_long(argc, argv,
                        "+:iL:o:qt:vhs:Vm",
                        cmdlineOptions, nullptr);
    // clang-format on

    main_optind = optind;

    Trace("options") << "[ got " << int(c) << " (" << char(c) << ") ]"
                     << "[ next option will be at pos: " << optind << " ]"
                     << std::endl;

    // The initial getopt_long call should always determine that argv[0]
    // is not an option and returns -1. We always manually advance beyond
    // this element.
    if (old_optind == 0 && c == -1)
    {
      Assert(main_optind > 0);
      continue;
    }

    if (c == -1)
    {
      if (TraceIsOn("options"))
      {
        Trace("options") << "done with option parsing" << std::endl;
        for (int index = optind; index < argc; ++index)
        {
          Trace("options") << "remaining " << argv[index] << std::endl;
        }
      }
      break;
    }

    std::string option = argv[old_optind == 0 ? 1 : old_optind];
    std::string optionarg = (optarg == nullptr) ? "" : optarg;

    Trace("preemptGetopt") << "processing option " << c << " (`" << char(c)
                           << "'), " << option << std::endl;

    switch (c)
    {
// clang-format off
    case 256: // --approx-branch-depth
      solver.setOption("approx-branch-depth", optionarg); break;
    case 257: // --arith-brab
      solver.setOption("arith-brab", "true"); break;
    case 258: // --no-arith-brab
      solver.setOption("arith-brab", "false"); break;
    case 259: // --arith-eq-solver
      solver.setOption("arith-eq-solver", "true"); break;
    case 260: // --no-arith-eq-solver
      solver.setOption("arith-eq-solver", "false"); break;
    case 261: // --arith-no-partial-fun
      solver.setOption("arith-no-partial-fun", "true"); break;
    case 262: // --no-arith-no-partial-fun
      solver.setOption("arith-no-partial-fun", "false"); break;
    case 263: // --arith-prop
      solver.setOption("arith-prop", optionarg); break;
    case 264: // --arith-prop-clauses
      solver.setOption("arith-prop-clauses", optionarg); break;
    case 265: // --arith-rewrite-equalities
      solver.setOption("arith-rewrite-equalities", "true"); break;
    case 266: // --no-arith-rewrite-equalities
      solver.setOption("arith-rewrite-equalities", "false"); break;
    case 267: // --arith-static-learning
      solver.setOption("arith-static-learning", "true"); break;
    case 268: // --no-arith-static-learning
      solver.setOption("arith-static-learning", "false"); break;
    case 269: // --collect-pivot-stats
      solver.setOption("collect-pivot-stats", "true"); break;
    case 270: // --no-collect-pivot-stats
      solver.setOption("collect-pivot-stats", "false"); break;
    case 271: // --cut-all-bounded
      solver.setOption("cut-all-bounded", "true"); break;
    case 272: // --no-cut-all-bounded
      solver.setOption("cut-all-bounded", "false"); break;
    case 273: // --dio-decomps
      solver.setOption("dio-decomps", "true"); break;
    case 274: // --no-dio-decomps
      solver.setOption("dio-decomps", "false"); break;
    case 275: // --dio-solver
      solver.setOption("dio-solver", "true"); break;
    case 276: // --no-dio-solver
      solver.setOption("dio-solver", "false"); break;
    case 277: // --dio-turns
      solver.setOption("dio-turns", optionarg); break;
    case 278: // --error-selection-rule
      solver.setOption("error-selection-rule", optionarg); break;
    case 279: // --fc-penalties
      solver.setOption("fc-penalties", "true"); break;
    case 280: // --no-fc-penalties
      solver.setOption("fc-penalties", "false"); break;
    case 281: // --heuristic-pivots
      solver.setOption("heuristic-pivots", optionarg); break;
    case 282: // --lemmas-on-replay-failure
      solver.setOption("lemmas-on-replay-failure", "true"); break;
    case 283: // --no-lemmas-on-replay-failure
      solver.setOption("lemmas-on-replay-failure", "false"); break;
    case 284: // --maxCutsInContext
      solver.setOption("maxCutsInContext", optionarg); break;
    case 285: // --miplib-trick
      solver.setOption("miplib-trick", "true"); break;
    case 286: // --no-miplib-trick
      solver.setOption("miplib-trick", "false"); break;
    case 287: // --miplib-trick-subs
      solver.setOption("miplib-trick-subs", optionarg); break;
    case 288: // --new-prop
      solver.setOption("new-prop", "true"); break;
    case 289: // --no-new-prop
      solver.setOption("new-prop", "false"); break;
    case 290: // --nl-cov
      solver.setOption("nl-cov", "true"); break;
    case 291: // --no-nl-cov
      solver.setOption("nl-cov", "false"); break;
    case 292: // --nl-cov-force
      solver.setOption("nl-cov-force", "true"); break;
    case 293: // --no-nl-cov-force
      solver.setOption("nl-cov-force", "false"); break;
    case 294: // --nl-cov-lift
      solver.setOption("nl-cov-lift", optionarg); break;
    case 295: // --nl-cov-linear-model
      solver.setOption("nl-cov-linear-model", optionarg); break;
    case 296: // --nl-cov-proj
      solver.setOption("nl-cov-proj", optionarg); break;
    case 297: // --nl-cov-prune
      solver.setOption("nl-cov-prune", "true"); break;
    case 298: // --no-nl-cov-prune
      solver.setOption("nl-cov-prune", "false"); break;
    case 299: // --nl-cov-var-elim
      solver.setOption("nl-cov-var-elim", "true"); break;
    case 300: // --no-nl-cov-var-elim
      solver.setOption("nl-cov-var-elim", "false"); break;
    case 301: // --nl-ext
      solver.setOption("nl-ext", optionarg); break;
    case 302: // --nl-ext-ent-conf
      solver.setOption("nl-ext-ent-conf", "true"); break;
    case 303: // --no-nl-ext-ent-conf
      solver.setOption("nl-ext-ent-conf", "false"); break;
    case 304: // --nl-ext-factor
      solver.setOption("nl-ext-factor", "true"); break;
    case 305: // --no-nl-ext-factor
      solver.setOption("nl-ext-factor", "false"); break;
    case 306: // --nl-ext-inc-prec
      solver.setOption("nl-ext-inc-prec", "true"); break;
    case 307: // --no-nl-ext-inc-prec
      solver.setOption("nl-ext-inc-prec", "false"); break;
    case 308: // --nl-ext-purify
      solver.setOption("nl-ext-purify", "true"); break;
    case 309: // --no-nl-ext-purify
      solver.setOption("nl-ext-purify", "false"); break;
    case 310: // --nl-ext-rbound
      solver.setOption("nl-ext-rbound", "true"); break;
    case 311: // --no-nl-ext-rbound
      solver.setOption("nl-ext-rbound", "false"); break;
    case 312: // --nl-ext-rewrite
      solver.setOption("nl-ext-rewrite", "true"); break;
    case 313: // --no-nl-ext-rewrite
      solver.setOption("nl-ext-rewrite", "false"); break;
    case 314: // --nl-ext-split-zero
      solver.setOption("nl-ext-split-zero", "true"); break;
    case 315: // --no-nl-ext-split-zero
      solver.setOption("nl-ext-split-zero", "false"); break;
    case 316: // --nl-ext-tf-taylor-deg
      solver.setOption("nl-ext-tf-taylor-deg", optionarg); break;
    case 317: // --nl-ext-tf-tplanes
      solver.setOption("nl-ext-tf-tplanes", "true"); break;
    case 318: // --no-nl-ext-tf-tplanes
      solver.setOption("nl-ext-tf-tplanes", "false"); break;
    case 319: // --nl-ext-tplanes
      solver.setOption("nl-ext-tplanes", "true"); break;
    case 320: // --no-nl-ext-tplanes
      solver.setOption("nl-ext-tplanes", "false"); break;
    case 321: // --nl-ext-tplanes-interleave
      solver.setOption("nl-ext-tplanes-interleave", "true"); break;
    case 322: // --no-nl-ext-tplanes-interleave
      solver.setOption("nl-ext-tplanes-interleave", "false"); break;
    case 323: // --nl-icp
      solver.setOption("nl-icp", "true"); break;
    case 324: // --no-nl-icp
      solver.setOption("nl-icp", "false"); break;
    case 325: // --nl-rlv
      solver.setOption("nl-rlv", optionarg); break;
    case 326: // --nl-rlv-assert-bounds
      solver.setOption("nl-rlv-assert-bounds", "true"); break;
    case 327: // --no-nl-rlv-assert-bounds
      solver.setOption("nl-rlv-assert-bounds", "false"); break;
    case 328: // --pb-rewrites
      solver.setOption("pb-rewrites", "true"); break;
    case 329: // --no-pb-rewrites
      solver.setOption("pb-rewrites", "false"); break;
    case 330: // --pivot-threshold
      solver.setOption("pivot-threshold", optionarg); break;
    case 331: // --pp-assert-max-sub-size
      solver.setOption("pp-assert-max-sub-size", optionarg); break;
    case 332: // --prop-row-length
      solver.setOption("prop-row-length", optionarg); break;
    case 333: // --replay-early-close-depth
      solver.setOption("replay-early-close-depth", optionarg); break;
    case 334: // --replay-lemma-reject-cut
      solver.setOption("replay-lemma-reject-cut", optionarg); break;
    case 335: // --replay-num-err-penalty
      solver.setOption("replay-num-err-penalty", optionarg); break;
    case 336: // --replay-reject-cut
      solver.setOption("replay-reject-cut", optionarg); break;
    case 337: // --restrict-pivots
      solver.setOption("restrict-pivots", "true"); break;
    case 338: // --no-restrict-pivots
      solver.setOption("restrict-pivots", "false"); break;
    case 339: // --revert-arith-models-on-unsat
      solver.setOption("revert-arith-models-on-unsat", "true"); break;
    case 340: // --no-revert-arith-models-on-unsat
      solver.setOption("revert-arith-models-on-unsat", "false"); break;
    case 341: // --rr-turns
      solver.setOption("rr-turns", optionarg); break;
    case 342: // --se-solve-int
      solver.setOption("se-solve-int", "true"); break;
    case 343: // --no-se-solve-int
      solver.setOption("se-solve-int", "false"); break;
    case 344: // --simplex-check-period
      solver.setOption("simplex-check-period", optionarg); break;
    case 345: // --soi-qe
      solver.setOption("soi-qe", "true"); break;
    case 346: // --no-soi-qe
      solver.setOption("soi-qe", "false"); break;
    case 347: // --standard-effort-variable-order-pivots
      solver.setOption("standard-effort-variable-order-pivots", optionarg); break;
    case 348: // --unate-lemmas
      solver.setOption("unate-lemmas", optionarg); break;
    case 349: // --use-approx
      solver.setOption("use-approx", "true"); break;
    case 350: // --no-use-approx
      solver.setOption("use-approx", "false"); break;
    case 351: // --use-fcsimplex
      solver.setOption("use-fcsimplex", "true"); break;
    case 352: // --no-use-fcsimplex
      solver.setOption("use-fcsimplex", "false"); break;
    case 353: // --use-soi
      solver.setOption("use-soi", "true"); break;
    case 354: // --no-use-soi
      solver.setOption("use-soi", "false"); break;
    case 355: // --arrays-eager-index
      solver.setOption("arrays-eager-index", "true"); break;
    case 356: // --no-arrays-eager-index
      solver.setOption("arrays-eager-index", "false"); break;
    case 357: // --arrays-eager-lemmas
      solver.setOption("arrays-eager-lemmas", "true"); break;
    case 358: // --no-arrays-eager-lemmas
      solver.setOption("arrays-eager-lemmas", "false"); break;
    case 359: // --arrays-exp
      solver.setOption("arrays-exp", "true"); break;
    case 360: // --no-arrays-exp
      solver.setOption("arrays-exp", "false"); break;
    case 361: // --arrays-optimize-linear
      solver.setOption("arrays-optimize-linear", "true"); break;
    case 362: // --no-arrays-optimize-linear
      solver.setOption("arrays-optimize-linear", "false"); break;
    case 363: // --arrays-prop
      solver.setOption("arrays-prop", optionarg); break;
    case 364: // --arrays-reduce-sharing
      solver.setOption("arrays-reduce-sharing", "true"); break;
    case 365: // --no-arrays-reduce-sharing
      solver.setOption("arrays-reduce-sharing", "false"); break;
    case 366: // --arrays-weak-equiv
      solver.setOption("arrays-weak-equiv", "true"); break;
    case 367: // --no-arrays-weak-equiv
      solver.setOption("arrays-weak-equiv", "false"); break;
    case 368: // --err
    case 369: // --diagnostic-output-channel
      solver.setOption("err", optionarg); break;
    case 370: // --in
      solver.setOption("in", optionarg); break;
    case 'i': // -i
    case 371: // --incremental
      solver.setOption("incremental", "true"); break;
    case 372: // --no-incremental
      solver.setOption("incremental", "false"); break;
    case 'L': // -L
    case 373: // --lang
    case 374: // --input-language
      solver.setOption("lang", optionarg); break;
    case 375: // --out
    case 376: // --regular-output-channel
      solver.setOption("out", optionarg); break;
    case 'o': // -o
    case 377: // --output
      solver.setOption("output", optionarg); break;
    case 378: // --parse-only
      solver.setOption("parse-only", "true"); break;
    case 379: // --no-parse-only
      solver.setOption("parse-only", "false"); break;
    case 380: // --preprocess-only
      solver.setOption("preprocess-only", "true"); break;
    case 381: // --no-preprocess-only
      solver.setOption("preprocess-only", "false"); break;
    case 'q': // -q
    case 382: // --quiet
      solver.setOption("quiet", "true"); break;
    case 383: // --rlimit
      solver.setOption("rlimit", optionarg); break;
    case 384: // --rlimit-per
    case 385: // --reproducible-resource-limit
      solver.setOption("rlimit-per", optionarg); break;
    case 386: // --rweight
      solver.setOption("rweight", optionarg); break;
    case 387: // --stats
      solver.setOption("stats", "true"); break;
    case 388: // --no-stats
      solver.setOption("stats", "false"); break;
    case 389: // --stats-all
      solver.setOption("stats-all", "true"); break;
    case 390: // --no-stats-all
      solver.setOption("stats-all", "false"); break;
    case 391: // --stats-every-query
      solver.setOption("stats-every-query", "true"); break;
    case 392: // --no-stats-every-query
      solver.setOption("stats-every-query", "false"); break;
    case 393: // --stats-internal
      solver.setOption("stats-internal", "true"); break;
    case 394: // --no-stats-internal
      solver.setOption("stats-internal", "false"); break;
    case 395: // --tlimit
      solver.setOption("tlimit", optionarg); break;
    case 396: // --tlimit-per
      solver.setOption("tlimit-per", optionarg); break;
    case 't': // -t
    case 397: // --trace
      solver.setOption("trace", optionarg); break;
    case 'v': // -v
    case 398: // --verbose
      solver.setOption("verbose", "true"); break;
    case 399: // --verbosity
      solver.setOption("verbosity", optionarg); break;
    case 400: // --bitblast
      solver.setOption("bitblast", optionarg); break;
    case 401: // --bitwise-eq
      solver.setOption("bitwise-eq", "true"); break;
    case 402: // --no-bitwise-eq
      solver.setOption("bitwise-eq", "false"); break;
    case 403: // --bool-to-bv
      solver.setOption("bool-to-bv", optionarg); break;
    case 404: // --bv-assert-input
      solver.setOption("bv-assert-input", "true"); break;
    case 405: // --no-bv-assert-input
      solver.setOption("bv-assert-input", "false"); break;
    case 406: // --bv-eager-eval
      solver.setOption("bv-eager-eval", "true"); break;
    case 407: // --no-bv-eager-eval
      solver.setOption("bv-eager-eval", "false"); break;
    case 408: // --bv-gauss-elim
      solver.setOption("bv-gauss-elim", "true"); break;
    case 409: // --no-bv-gauss-elim
      solver.setOption("bv-gauss-elim", "false"); break;
    case 410: // --bv-intro-pow2
      solver.setOption("bv-intro-pow2", "true"); break;
    case 411: // --no-bv-intro-pow2
      solver.setOption("bv-intro-pow2", "false"); break;
    case 412: // --bv-propagate
      solver.setOption("bv-propagate", "true"); break;
    case 413: // --no-bv-propagate
      solver.setOption("bv-propagate", "false"); break;
    case 414: // --bv-rw-extend-eq
      solver.setOption("bv-rw-extend-eq", "true"); break;
    case 415: // --no-bv-rw-extend-eq
      solver.setOption("bv-rw-extend-eq", "false"); break;
    case 416: // --bv-sat-solver
      solver.setOption("bv-sat-solver", optionarg); break;
    case 417: // --bv-solver
      solver.setOption("bv-solver", optionarg); break;
    case 418: // --bv-to-bool
      solver.setOption("bv-to-bool", "true"); break;
    case 419: // --no-bv-to-bool
      solver.setOption("bv-to-bool", "false"); break;
    case 420: // --cdt-bisimilar
      solver.setOption("cdt-bisimilar", "true"); break;
    case 421: // --no-cdt-bisimilar
      solver.setOption("cdt-bisimilar", "false"); break;
    case 422: // --dt-binary-split
      solver.setOption("dt-binary-split", "true"); break;
    case 423: // --no-dt-binary-split
      solver.setOption("dt-binary-split", "false"); break;
    case 424: // --dt-blast-splits
      solver.setOption("dt-blast-splits", "true"); break;
    case 425: // --no-dt-blast-splits
      solver.setOption("dt-blast-splits", "false"); break;
    case 426: // --dt-cyclic
      solver.setOption("dt-cyclic", "true"); break;
    case 427: // --no-dt-cyclic
      solver.setOption("dt-cyclic", "false"); break;
    case 428: // --dt-infer-as-lemmas
      solver.setOption("dt-infer-as-lemmas", "true"); break;
    case 429: // --no-dt-infer-as-lemmas
      solver.setOption("dt-infer-as-lemmas", "false"); break;
    case 430: // --dt-nested-rec
      solver.setOption("dt-nested-rec", "true"); break;
    case 431: // --no-dt-nested-rec
      solver.setOption("dt-nested-rec", "false"); break;
    case 432: // --dt-polite-optimize
      solver.setOption("dt-polite-optimize", "true"); break;
    case 433: // --no-dt-polite-optimize
      solver.setOption("dt-polite-optimize", "false"); break;
    case 434: // --dt-share-sel
      solver.setOption("dt-share-sel", "true"); break;
    case 435: // --no-dt-share-sel
      solver.setOption("dt-share-sel", "false"); break;
    case 436: // --sygus-abort-size
      solver.setOption("sygus-abort-size", optionarg); break;
    case 437: // --sygus-fair
      solver.setOption("sygus-fair", optionarg); break;
    case 438: // --sygus-fair-max
      solver.setOption("sygus-fair-max", "true"); break;
    case 439: // --no-sygus-fair-max
      solver.setOption("sygus-fair-max", "false"); break;
    case 440: // --sygus-rewriter
      solver.setOption("sygus-rewriter", optionarg); break;
    case 441: // --sygus-simple-sym-break
      solver.setOption("sygus-simple-sym-break", optionarg); break;
    case 442: // --sygus-sym-break-lazy
      solver.setOption("sygus-sym-break-lazy", "true"); break;
    case 443: // --no-sygus-sym-break-lazy
      solver.setOption("sygus-sym-break-lazy", "false"); break;
    case 444: // --sygus-sym-break-pbe
      solver.setOption("sygus-sym-break-pbe", "true"); break;
    case 445: // --no-sygus-sym-break-pbe
      solver.setOption("sygus-sym-break-pbe", "false"); break;
    case 446: // --sygus-sym-break-rlv
      solver.setOption("sygus-sym-break-rlv", "true"); break;
    case 447: // --no-sygus-sym-break-rlv
      solver.setOption("sygus-sym-break-rlv", "false"); break;
    case 448: // --decision
    case 449: // --decision-mode
      solver.setOption("decision", optionarg); break;
    case 450: // --jh-rlv-order
      solver.setOption("jh-rlv-order", "true"); break;
    case 451: // --no-jh-rlv-order
      solver.setOption("jh-rlv-order", "false"); break;
    case 452: // --jh-skolem
      solver.setOption("jh-skolem", optionarg); break;
    case 453: // --jh-skolem-rlv
      solver.setOption("jh-skolem-rlv", optionarg); break;
    case 454: // --type-checking
      solver.setOption("type-checking", "true"); break;
    case 455: // --no-type-checking
      solver.setOption("type-checking", "false"); break;
    case 456: // --wf-checking
      solver.setOption("wf-checking", "true"); break;
    case 457: // --no-wf-checking
      solver.setOption("wf-checking", "false"); break;
    case 458: // --ff-field-polys
      solver.setOption("ff-field-polys", "true"); break;
    case 459: // --no-ff-field-polys
      solver.setOption("ff-field-polys", "false"); break;
    case 460: // --ff-trace-gb
      solver.setOption("ff-trace-gb", "true"); break;
    case 461: // --no-ff-trace-gb
      solver.setOption("ff-trace-gb", "false"); break;
    case 462: // --fp-exp
      solver.setOption("fp-exp", "true"); break;
    case 463: // --no-fp-exp
      solver.setOption("fp-exp", "false"); break;
    case 464: // --fp-lazy-wb
      solver.setOption("fp-lazy-wb", "true"); break;
    case 465: // --no-fp-lazy-wb
      solver.setOption("fp-lazy-wb", "false"); break;
    case 466: // --copyright
      solver.setOption("copyright", "true"); break;
    case 467: // --dump-difficulty
      solver.setOption("dump-difficulty", "true"); break;
    case 468: // --no-dump-difficulty
      solver.setOption("dump-difficulty", "false"); break;
    case 469: // --dump-instantiations
      solver.setOption("dump-instantiations", "true"); break;
    case 470: // --no-dump-instantiations
      solver.setOption("dump-instantiations", "false"); break;
    case 471: // --dump-instantiations-debug
      solver.setOption("dump-instantiations-debug", "true"); break;
    case 472: // --no-dump-instantiations-debug
      solver.setOption("dump-instantiations-debug", "false"); break;
    case 473: // --dump-models
      solver.setOption("dump-models", "true"); break;
    case 474: // --no-dump-models
      solver.setOption("dump-models", "false"); break;
    case 475: // --dump-proofs
      solver.setOption("dump-proofs", "true"); break;
    case 476: // --no-dump-proofs
      solver.setOption("dump-proofs", "false"); break;
    case 477: // --dump-unsat-cores
      solver.setOption("dump-unsat-cores", "true"); break;
    case 478: // --no-dump-unsat-cores
      solver.setOption("dump-unsat-cores", "false"); break;
    case 479: // --early-exit
      solver.setOption("early-exit", "true"); break;
    case 480: // --no-early-exit
      solver.setOption("early-exit", "false"); break;
    case 481: // --filename
      solver.setOption("filename", optionarg); break;
    case 482: // --force-no-limit-cpu-while-dump
      solver.setOption("force-no-limit-cpu-while-dump", "true"); break;
    case 483: // --no-force-no-limit-cpu-while-dump
      solver.setOption("force-no-limit-cpu-while-dump", "false"); break;
    case 'h': // -h
    case 484: // --help
      solver.setOption("help", "true"); break;
    case 485: // --interactive
      solver.setOption("interactive", "true"); break;
    case 486: // --no-interactive
      solver.setOption("interactive", "false"); break;
    case 487: // --portfolio-jobs
      solver.setOption("portfolio-jobs", optionarg); break;
    case 488: // --print-success
      solver.setOption("print-success", "true"); break;
    case 489: // --no-print-success
      solver.setOption("print-success", "false"); break;
    case 's': // -s
    case 490: // --seed
      solver.setOption("seed", optionarg); break;
    case 491: // --segv-spin
      solver.setOption("segv-spin", "true"); break;
    case 492: // --no-segv-spin
      solver.setOption("segv-spin", "false"); break;
    case 493: // --show-config
      solver.setOption("show-config", "true"); break;
    case 494: // --show-trace-tags
      solver.setOption("show-trace-tags", "true"); break;
    case 495: // --stdin-input-per-line
      solver.setOption("stdin-input-per-line", "true"); break;
    case 496: // --no-stdin-input-per-line
      solver.setOption("stdin-input-per-line", "false"); break;
    case 497: // --use-portfolio
      solver.setOption("use-portfolio", "true"); break;
    case 498: // --no-use-portfolio
      solver.setOption("use-portfolio", "false"); break;
    case 'V': // -V
    case 499: // --version
      solver.setOption("version", "true"); break;
    case 500: // --append-learned-literals-to-cubes
      solver.setOption("append-learned-literals-to-cubes", "true"); break;
    case 501: // --no-append-learned-literals-to-cubes
      solver.setOption("append-learned-literals-to-cubes", "false"); break;
    case 502: // --checks-before-partition
      solver.setOption("checks-before-partition", optionarg); break;
    case 503: // --checks-between-partitions
      solver.setOption("checks-between-partitions", optionarg); break;
    case 504: // --compute-partitions
      solver.setOption("compute-partitions", optionarg); break;
    case 505: // --partition-check
    case 506: // --check
      solver.setOption("partition-check", optionarg); break;
    case 507: // --partition-conflict-size
      solver.setOption("partition-conflict-size", optionarg); break;
    case 508: // --partition-strategy
    case 509: // --partition
      solver.setOption("partition-strategy", optionarg); break;
    case 510: // --write-partitions-to
    case 511: // --partitions-out
      solver.setOption("write-partitions-to", optionarg); break;
    case 512: // --filesystem-access
      solver.setOption("filesystem-access", "true"); break;
    case 513: // --no-filesystem-access
      solver.setOption("filesystem-access", "false"); break;
    case 514: // --flex-parser
      solver.setOption("flex-parser", "true"); break;
    case 515: // --no-flex-parser
      solver.setOption("flex-parser", "false"); break;
    case 516: // --force-logic
      solver.setOption("force-logic", optionarg); break;
    case 517: // --global-declarations
      solver.setOption("global-declarations", "true"); break;
    case 518: // --no-global-declarations
      solver.setOption("global-declarations", "false"); break;
    case 519: // --semantic-checks
      solver.setOption("semantic-checks", "true"); break;
    case 520: // --no-semantic-checks
      solver.setOption("semantic-checks", "false"); break;
    case 521: // --strict-parsing
      solver.setOption("strict-parsing", "true"); break;
    case 522: // --no-strict-parsing
      solver.setOption("strict-parsing", "false"); break;
    case 523: // --bv-print-consts-as-indexed-symbols
      solver.setOption("bv-print-consts-as-indexed-symbols", "true"); break;
    case 524: // --no-bv-print-consts-as-indexed-symbols
      solver.setOption("bv-print-consts-as-indexed-symbols", "false"); break;
    case 525: // --dag-thresh
      solver.setOption("dag-thresh", optionarg); break;
    case 526: // --expr-depth
      solver.setOption("expr-depth", optionarg); break;
    case 527: // --flatten-ho-chains
      solver.setOption("flatten-ho-chains", "true"); break;
    case 528: // --no-flatten-ho-chains
      solver.setOption("flatten-ho-chains", "false"); break;
    case 529: // --model-u-print
      solver.setOption("model-u-print", optionarg); break;
    case 530: // --output-lang
    case 531: // --output-language
      solver.setOption("output-lang", optionarg); break;
    case 532: // --check-proof-steps
      solver.setOption("check-proof-steps", "true"); break;
    case 533: // --no-check-proof-steps
      solver.setOption("check-proof-steps", "false"); break;
    case 534: // --lfsc-expand-trust
      solver.setOption("lfsc-expand-trust", "true"); break;
    case 535: // --no-lfsc-expand-trust
      solver.setOption("lfsc-expand-trust", "false"); break;
    case 536: // --lfsc-flatten
      solver.setOption("lfsc-flatten", "true"); break;
    case 537: // --no-lfsc-flatten
      solver.setOption("lfsc-flatten", "false"); break;
    case 538: // --opt-res-reconstruction-size
      solver.setOption("opt-res-reconstruction-size", "true"); break;
    case 539: // --no-opt-res-reconstruction-size
      solver.setOption("opt-res-reconstruction-size", "false"); break;
    case 540: // --print-dot-clusters
      solver.setOption("print-dot-clusters", "true"); break;
    case 541: // --no-print-dot-clusters
      solver.setOption("print-dot-clusters", "false"); break;
    case 542: // --proof-alethe-res-pivots
      solver.setOption("proof-alethe-res-pivots", "true"); break;
    case 543: // --no-proof-alethe-res-pivots
      solver.setOption("proof-alethe-res-pivots", "false"); break;
    case 544: // --proof-annotate
      solver.setOption("proof-annotate", "true"); break;
    case 545: // --no-proof-annotate
      solver.setOption("proof-annotate", "false"); break;
    case 546: // --proof-check
      solver.setOption("proof-check", optionarg); break;
    case 547: // --proof-dot-dag
      solver.setOption("proof-dot-dag", "true"); break;
    case 548: // --no-proof-dot-dag
      solver.setOption("proof-dot-dag", "false"); break;
    case 549: // --proof-format-mode
      solver.setOption("proof-format-mode", optionarg); break;
    case 550: // --proof-granularity
      solver.setOption("proof-granularity", optionarg); break;
    case 551: // --proof-pedantic
      solver.setOption("proof-pedantic", optionarg); break;
    case 552: // --proof-pp-merge
      solver.setOption("proof-pp-merge", "true"); break;
    case 553: // --no-proof-pp-merge
      solver.setOption("proof-pp-merge", "false"); break;
    case 554: // --proof-print-conclusion
      solver.setOption("proof-print-conclusion", "true"); break;
    case 555: // --no-proof-print-conclusion
      solver.setOption("proof-print-conclusion", "false"); break;
    case 556: // --proof-prune-input
      solver.setOption("proof-prune-input", "true"); break;
    case 557: // --no-proof-prune-input
      solver.setOption("proof-prune-input", "false"); break;
    case 558: // --proof-rewrite-rcons-limit
      solver.setOption("proof-rewrite-rcons-limit", optionarg); break;
    case 559: // --minisat-dump-dimacs
      solver.setOption("minisat-dump-dimacs", "true"); break;
    case 560: // --no-minisat-dump-dimacs
      solver.setOption("minisat-dump-dimacs", "false"); break;
    case 561: // --minisat-simplification
      solver.setOption("minisat-simplification", optionarg); break;
    case 562: // --preregister-mode
      solver.setOption("preregister-mode", optionarg); break;
    case 563: // --random-freq
    case 564: // --random-frequency
      solver.setOption("random-freq", optionarg); break;
    case 565: // --restart-int-base
      solver.setOption("restart-int-base", optionarg); break;
    case 566: // --restart-int-inc
      solver.setOption("restart-int-inc", optionarg); break;
    case 567: // --sat-random-seed
      solver.setOption("sat-random-seed", optionarg); break;
    case 568: // --cbqi
      solver.setOption("cbqi", "true"); break;
    case 569: // --no-cbqi
      solver.setOption("cbqi", "false"); break;
    case 570: // --cbqi-all-conflict
      solver.setOption("cbqi-all-conflict", "true"); break;
    case 571: // --no-cbqi-all-conflict
      solver.setOption("cbqi-all-conflict", "false"); break;
    case 572: // --cbqi-eager-check-rd
      solver.setOption("cbqi-eager-check-rd", "true"); break;
    case 573: // --no-cbqi-eager-check-rd
      solver.setOption("cbqi-eager-check-rd", "false"); break;
    case 574: // --cbqi-eager-test
      solver.setOption("cbqi-eager-test", "true"); break;
    case 575: // --no-cbqi-eager-test
      solver.setOption("cbqi-eager-test", "false"); break;
    case 576: // --cbqi-mode
      solver.setOption("cbqi-mode", optionarg); break;
    case 577: // --cbqi-skip-rd
      solver.setOption("cbqi-skip-rd", "true"); break;
    case 578: // --no-cbqi-skip-rd
      solver.setOption("cbqi-skip-rd", "false"); break;
    case 579: // --cbqi-tconstraint
      solver.setOption("cbqi-tconstraint", "true"); break;
    case 580: // --no-cbqi-tconstraint
      solver.setOption("cbqi-tconstraint", "false"); break;
    case 581: // --cbqi-vo-exp
      solver.setOption("cbqi-vo-exp", "true"); break;
    case 582: // --no-cbqi-vo-exp
      solver.setOption("cbqi-vo-exp", "false"); break;
    case 583: // --cegis-sample
      solver.setOption("cegis-sample", optionarg); break;
    case 584: // --cegqi
      solver.setOption("cegqi", "true"); break;
    case 585: // --no-cegqi
      solver.setOption("cegqi", "false"); break;
    case 586: // --cegqi-all
      solver.setOption("cegqi-all", "true"); break;
    case 587: // --no-cegqi-all
      solver.setOption("cegqi-all", "false"); break;
    case 588: // --cegqi-bv
      solver.setOption("cegqi-bv", "true"); break;
    case 589: // --no-cegqi-bv
      solver.setOption("cegqi-bv", "false"); break;
    case 590: // --cegqi-bv-concat-inv
      solver.setOption("cegqi-bv-concat-inv", "true"); break;
    case 591: // --no-cegqi-bv-concat-inv
      solver.setOption("cegqi-bv-concat-inv", "false"); break;
    case 592: // --cegqi-bv-ineq
      solver.setOption("cegqi-bv-ineq", optionarg); break;
    case 593: // --cegqi-bv-interleave-value
      solver.setOption("cegqi-bv-interleave-value", "true"); break;
    case 594: // --no-cegqi-bv-interleave-value
      solver.setOption("cegqi-bv-interleave-value", "false"); break;
    case 595: // --cegqi-bv-linear
      solver.setOption("cegqi-bv-linear", "true"); break;
    case 596: // --no-cegqi-bv-linear
      solver.setOption("cegqi-bv-linear", "false"); break;
    case 597: // --cegqi-bv-rm-extract
      solver.setOption("cegqi-bv-rm-extract", "true"); break;
    case 598: // --no-cegqi-bv-rm-extract
      solver.setOption("cegqi-bv-rm-extract", "false"); break;
    case 599: // --cegqi-bv-solve-nl
      solver.setOption("cegqi-bv-solve-nl", "true"); break;
    case 600: // --no-cegqi-bv-solve-nl
      solver.setOption("cegqi-bv-solve-nl", "false"); break;
    case 601: // --cegqi-full
      solver.setOption("cegqi-full", "true"); break;
    case 602: // --no-cegqi-full
      solver.setOption("cegqi-full", "false"); break;
    case 603: // --cegqi-inf-int
      solver.setOption("cegqi-inf-int", "true"); break;
    case 604: // --no-cegqi-inf-int
      solver.setOption("cegqi-inf-int", "false"); break;
    case 605: // --cegqi-inf-real
      solver.setOption("cegqi-inf-real", "true"); break;
    case 606: // --no-cegqi-inf-real
      solver.setOption("cegqi-inf-real", "false"); break;
    case 607: // --cegqi-innermost
      solver.setOption("cegqi-innermost", "true"); break;
    case 608: // --no-cegqi-innermost
      solver.setOption("cegqi-innermost", "false"); break;
    case 609: // --cegqi-midpoint
      solver.setOption("cegqi-midpoint", "true"); break;
    case 610: // --no-cegqi-midpoint
      solver.setOption("cegqi-midpoint", "false"); break;
    case 611: // --cegqi-min-bounds
      solver.setOption("cegqi-min-bounds", "true"); break;
    case 612: // --no-cegqi-min-bounds
      solver.setOption("cegqi-min-bounds", "false"); break;
    case 613: // --cegqi-multi-inst
      solver.setOption("cegqi-multi-inst", "true"); break;
    case 614: // --no-cegqi-multi-inst
      solver.setOption("cegqi-multi-inst", "false"); break;
    case 615: // --cegqi-nested-qe
      solver.setOption("cegqi-nested-qe", "true"); break;
    case 616: // --no-cegqi-nested-qe
      solver.setOption("cegqi-nested-qe", "false"); break;
    case 617: // --cegqi-nopt
      solver.setOption("cegqi-nopt", "true"); break;
    case 618: // --no-cegqi-nopt
      solver.setOption("cegqi-nopt", "false"); break;
    case 619: // --cegqi-round-up-lia
      solver.setOption("cegqi-round-up-lia", "true"); break;
    case 620: // --no-cegqi-round-up-lia
      solver.setOption("cegqi-round-up-lia", "false"); break;
    case 621: // --cond-var-split-quant
      solver.setOption("cond-var-split-quant", optionarg); break;
    case 622: // --conjecture-gen
      solver.setOption("conjecture-gen", "true"); break;
    case 623: // --no-conjecture-gen
      solver.setOption("conjecture-gen", "false"); break;
    case 624: // --conjecture-gen-gt-enum
      solver.setOption("conjecture-gen-gt-enum", optionarg); break;
    case 625: // --conjecture-gen-max-depth
      solver.setOption("conjecture-gen-max-depth", optionarg); break;
    case 626: // --conjecture-gen-per-round
      solver.setOption("conjecture-gen-per-round", optionarg); break;
    case 627: // --cons-exp-triggers
      solver.setOption("cons-exp-triggers", "true"); break;
    case 628: // --no-cons-exp-triggers
      solver.setOption("cons-exp-triggers", "false"); break;
    case 629: // --dt-stc-ind
      solver.setOption("dt-stc-ind", "true"); break;
    case 630: // --no-dt-stc-ind
      solver.setOption("dt-stc-ind", "false"); break;
    case 631: // --dt-var-exp-quant
      solver.setOption("dt-var-exp-quant", "true"); break;
    case 632: // --no-dt-var-exp-quant
      solver.setOption("dt-var-exp-quant", "false"); break;
    case 633: // --e-matching
      solver.setOption("e-matching", "true"); break;
    case 634: // --no-e-matching
      solver.setOption("e-matching", "false"); break;
    case 635: // --elim-taut-quant
      solver.setOption("elim-taut-quant", "true"); break;
    case 636: // --no-elim-taut-quant
      solver.setOption("elim-taut-quant", "false"); break;
    case 637: // --enum-inst
      solver.setOption("enum-inst", "true"); break;
    case 638: // --no-enum-inst
      solver.setOption("enum-inst", "false"); break;
    case 639: // --enum-inst-interleave
      solver.setOption("enum-inst-interleave", "true"); break;
    case 640: // --no-enum-inst-interleave
      solver.setOption("enum-inst-interleave", "false"); break;
    case 641: // --enum-inst-limit
      solver.setOption("enum-inst-limit", optionarg); break;
    case 642: // --enum-inst-rd
      solver.setOption("enum-inst-rd", "true"); break;
    case 643: // --no-enum-inst-rd
      solver.setOption("enum-inst-rd", "false"); break;
    case 644: // --enum-inst-stratify
      solver.setOption("enum-inst-stratify", "true"); break;
    case 645: // --no-enum-inst-stratify
      solver.setOption("enum-inst-stratify", "false"); break;
    case 646: // --enum-inst-sum
      solver.setOption("enum-inst-sum", "true"); break;
    case 647: // --no-enum-inst-sum
      solver.setOption("enum-inst-sum", "false"); break;
    case 648: // --ext-rewrite-quant
      solver.setOption("ext-rewrite-quant", "true"); break;
    case 649: // --no-ext-rewrite-quant
      solver.setOption("ext-rewrite-quant", "false"); break;
    case 650: // --finite-model-find
      solver.setOption("finite-model-find", "true"); break;
    case 651: // --no-finite-model-find
      solver.setOption("finite-model-find", "false"); break;
    case 652: // --fmf-bound
      solver.setOption("fmf-bound", "true"); break;
    case 653: // --no-fmf-bound
      solver.setOption("fmf-bound", "false"); break;
    case 654: // --fmf-bound-blast
      solver.setOption("fmf-bound-blast", "true"); break;
    case 655: // --no-fmf-bound-blast
      solver.setOption("fmf-bound-blast", "false"); break;
    case 656: // --fmf-bound-lazy
      solver.setOption("fmf-bound-lazy", "true"); break;
    case 657: // --no-fmf-bound-lazy
      solver.setOption("fmf-bound-lazy", "false"); break;
    case 658: // --fmf-fun
      solver.setOption("fmf-fun", "true"); break;
    case 659: // --no-fmf-fun
      solver.setOption("fmf-fun", "false"); break;
    case 660: // --fmf-fun-rlv
      solver.setOption("fmf-fun-rlv", "true"); break;
    case 661: // --no-fmf-fun-rlv
      solver.setOption("fmf-fun-rlv", "false"); break;
    case 662: // --fmf-mbqi
      solver.setOption("fmf-mbqi", optionarg); break;
    case 663: // --fmf-type-completion-thresh
      solver.setOption("fmf-type-completion-thresh", optionarg); break;
    case 664: // --full-saturate-quant
      solver.setOption("full-saturate-quant", "true"); break;
    case 665: // --no-full-saturate-quant
      solver.setOption("full-saturate-quant", "false"); break;
    case 666: // --global-negate
      solver.setOption("global-negate", "true"); break;
    case 667: // --no-global-negate
      solver.setOption("global-negate", "false"); break;
    case 668: // --ho-elim
      solver.setOption("ho-elim", "true"); break;
    case 669: // --no-ho-elim
      solver.setOption("ho-elim", "false"); break;
    case 670: // --ho-elim-store-ax
      solver.setOption("ho-elim-store-ax", "true"); break;
    case 671: // --no-ho-elim-store-ax
      solver.setOption("ho-elim-store-ax", "false"); break;
    case 672: // --ho-matching
      solver.setOption("ho-matching", "true"); break;
    case 673: // --no-ho-matching
      solver.setOption("ho-matching", "false"); break;
    case 674: // --ho-merge-term-db
      solver.setOption("ho-merge-term-db", "true"); break;
    case 675: // --no-ho-merge-term-db
      solver.setOption("ho-merge-term-db", "false"); break;
    case 676: // --ieval
      solver.setOption("ieval", optionarg); break;
    case 677: // --increment-triggers
      solver.setOption("increment-triggers", "true"); break;
    case 678: // --no-increment-triggers
      solver.setOption("increment-triggers", "false"); break;
    case 679: // --inst-max-level
      solver.setOption("inst-max-level", optionarg); break;
    case 680: // --inst-max-rounds
      solver.setOption("inst-max-rounds", optionarg); break;
    case 681: // --inst-no-entail
      solver.setOption("inst-no-entail", "true"); break;
    case 682: // --no-inst-no-entail
      solver.setOption("inst-no-entail", "false"); break;
    case 683: // --inst-when
      solver.setOption("inst-when", optionarg); break;
    case 684: // --inst-when-phase
      solver.setOption("inst-when-phase", optionarg); break;
    case 685: // --int-wf-ind
      solver.setOption("int-wf-ind", "true"); break;
    case 686: // --no-int-wf-ind
      solver.setOption("int-wf-ind", "false"); break;
    case 687: // --ite-dtt-split-quant
      solver.setOption("ite-dtt-split-quant", "true"); break;
    case 688: // --no-ite-dtt-split-quant
      solver.setOption("ite-dtt-split-quant", "false"); break;
    case 689: // --ite-lift-quant
      solver.setOption("ite-lift-quant", optionarg); break;
    case 690: // --literal-matching
      solver.setOption("literal-matching", optionarg); break;
    case 691: // --macros-quant
      solver.setOption("macros-quant", "true"); break;
    case 692: // --no-macros-quant
      solver.setOption("macros-quant", "false"); break;
    case 693: // --macros-quant-mode
      solver.setOption("macros-quant-mode", optionarg); break;
    case 694: // --mbqi
      solver.setOption("mbqi", "true"); break;
    case 695: // --no-mbqi
      solver.setOption("mbqi", "false"); break;
    case 696: // --mbqi-interleave
      solver.setOption("mbqi-interleave", "true"); break;
    case 697: // --no-mbqi-interleave
      solver.setOption("mbqi-interleave", "false"); break;
    case 698: // --mbqi-one-inst-per-round
      solver.setOption("mbqi-one-inst-per-round", "true"); break;
    case 699: // --no-mbqi-one-inst-per-round
      solver.setOption("mbqi-one-inst-per-round", "false"); break;
    case 700: // --miniscope-quant
      solver.setOption("miniscope-quant", optionarg); break;
    case 701: // --multi-trigger-cache
      solver.setOption("multi-trigger-cache", "true"); break;
    case 702: // --no-multi-trigger-cache
      solver.setOption("multi-trigger-cache", "false"); break;
    case 703: // --multi-trigger-linear
      solver.setOption("multi-trigger-linear", "true"); break;
    case 704: // --no-multi-trigger-linear
      solver.setOption("multi-trigger-linear", "false"); break;
    case 705: // --multi-trigger-priority
      solver.setOption("multi-trigger-priority", "true"); break;
    case 706: // --no-multi-trigger-priority
      solver.setOption("multi-trigger-priority", "false"); break;
    case 707: // --multi-trigger-when-single
      solver.setOption("multi-trigger-when-single", "true"); break;
    case 708: // --no-multi-trigger-when-single
      solver.setOption("multi-trigger-when-single", "false"); break;
    case 709: // --oracles
      solver.setOption("oracles", "true"); break;
    case 710: // --no-oracles
      solver.setOption("oracles", "false"); break;
    case 711: // --partial-triggers
      solver.setOption("partial-triggers", "true"); break;
    case 712: // --no-partial-triggers
      solver.setOption("partial-triggers", "false"); break;
    case 713: // --pool-inst
      solver.setOption("pool-inst", "true"); break;
    case 714: // --no-pool-inst
      solver.setOption("pool-inst", "false"); break;
    case 715: // --pre-skolem-quant
      solver.setOption("pre-skolem-quant", optionarg); break;
    case 716: // --pre-skolem-quant-nested
      solver.setOption("pre-skolem-quant-nested", "true"); break;
    case 717: // --no-pre-skolem-quant-nested
      solver.setOption("pre-skolem-quant-nested", "false"); break;
    case 718: // --prenex-quant
      solver.setOption("prenex-quant", optionarg); break;
    case 719: // --prenex-quant-user
      solver.setOption("prenex-quant-user", "true"); break;
    case 720: // --no-prenex-quant-user
      solver.setOption("prenex-quant-user", "false"); break;
    case 721: // --print-inst
      solver.setOption("print-inst", optionarg); break;
    case 722: // --print-inst-full
      solver.setOption("print-inst-full", "true"); break;
    case 723: // --no-print-inst-full
      solver.setOption("print-inst-full", "false"); break;
    case 724: // --purify-triggers
      solver.setOption("purify-triggers", "true"); break;
    case 725: // --no-purify-triggers
      solver.setOption("purify-triggers", "false"); break;
    case 726: // --quant-alpha-equiv
      solver.setOption("quant-alpha-equiv", "true"); break;
    case 727: // --no-quant-alpha-equiv
      solver.setOption("quant-alpha-equiv", "false"); break;
    case 728: // --quant-dsplit
      solver.setOption("quant-dsplit", optionarg); break;
    case 729: // --quant-fun-wd
      solver.setOption("quant-fun-wd", "true"); break;
    case 730: // --no-quant-fun-wd
      solver.setOption("quant-fun-wd", "false"); break;
    case 731: // --quant-ind
      solver.setOption("quant-ind", "true"); break;
    case 732: // --no-quant-ind
      solver.setOption("quant-ind", "false"); break;
    case 733: // --quant-rep-mode
      solver.setOption("quant-rep-mode", optionarg); break;
    case 734: // --register-quant-body-terms
      solver.setOption("register-quant-body-terms", "true"); break;
    case 735: // --no-register-quant-body-terms
      solver.setOption("register-quant-body-terms", "false"); break;
    case 736: // --relational-triggers
      solver.setOption("relational-triggers", "true"); break;
    case 737: // --no-relational-triggers
      solver.setOption("relational-triggers", "false"); break;
    case 738: // --relevant-triggers
      solver.setOption("relevant-triggers", "true"); break;
    case 739: // --no-relevant-triggers
      solver.setOption("relevant-triggers", "false"); break;
    case 740: // --sygus
      solver.setOption("sygus", "true"); break;
    case 741: // --no-sygus
      solver.setOption("sygus", "false"); break;
    case 742: // --sygus-add-const-grammar
      solver.setOption("sygus-add-const-grammar", "true"); break;
    case 743: // --no-sygus-add-const-grammar
      solver.setOption("sygus-add-const-grammar", "false"); break;
    case 744: // --sygus-arg-relevant
      solver.setOption("sygus-arg-relevant", "true"); break;
    case 745: // --no-sygus-arg-relevant
      solver.setOption("sygus-arg-relevant", "false"); break;
    case 746: // --sygus-auto-unfold
      solver.setOption("sygus-auto-unfold", "true"); break;
    case 747: // --no-sygus-auto-unfold
      solver.setOption("sygus-auto-unfold", "false"); break;
    case 748: // --sygus-bool-ite-return-const
      solver.setOption("sygus-bool-ite-return-const", "true"); break;
    case 749: // --no-sygus-bool-ite-return-const
      solver.setOption("sygus-bool-ite-return-const", "false"); break;
    case 750: // --sygus-core-connective
      solver.setOption("sygus-core-connective", "true"); break;
    case 751: // --no-sygus-core-connective
      solver.setOption("sygus-core-connective", "false"); break;
    case 752: // --sygus-crepair-abort
      solver.setOption("sygus-crepair-abort", "true"); break;
    case 753: // --no-sygus-crepair-abort
      solver.setOption("sygus-crepair-abort", "false"); break;
    case 754: // --sygus-enum
      solver.setOption("sygus-enum", optionarg); break;
    case 755: // --sygus-enum-fast-num-consts
      solver.setOption("sygus-enum-fast-num-consts", optionarg); break;
    case 756: // --sygus-enum-random-p
      solver.setOption("sygus-enum-random-p", optionarg); break;
    case 757: // --sygus-eval-unfold
      solver.setOption("sygus-eval-unfold", optionarg); break;
    case 758: // --sygus-expr-miner-check-timeout
      solver.setOption("sygus-expr-miner-check-timeout", optionarg); break;
    case 759: // --sygus-filter-sol
      solver.setOption("sygus-filter-sol", optionarg); break;
    case 760: // --sygus-filter-sol-rev
      solver.setOption("sygus-filter-sol-rev", "true"); break;
    case 761: // --no-sygus-filter-sol-rev
      solver.setOption("sygus-filter-sol-rev", "false"); break;
    case 762: // --sygus-grammar-cons
      solver.setOption("sygus-grammar-cons", optionarg); break;
    case 763: // --sygus-grammar-norm
      solver.setOption("sygus-grammar-norm", "true"); break;
    case 764: // --no-sygus-grammar-norm
      solver.setOption("sygus-grammar-norm", "false"); break;
    case 765: // --sygus-inference
      solver.setOption("sygus-inference", "true"); break;
    case 766: // --no-sygus-inference
      solver.setOption("sygus-inference", "false"); break;
    case 767: // --sygus-inst
      solver.setOption("sygus-inst", "true"); break;
    case 768: // --no-sygus-inst
      solver.setOption("sygus-inst", "false"); break;
    case 769: // --sygus-inst-mode
      solver.setOption("sygus-inst-mode", optionarg); break;
    case 770: // --sygus-inst-scope
      solver.setOption("sygus-inst-scope", optionarg); break;
    case 771: // --sygus-inst-term-sel
      solver.setOption("sygus-inst-term-sel", optionarg); break;
    case 772: // --sygus-inv-templ
      solver.setOption("sygus-inv-templ", optionarg); break;
    case 773: // --sygus-inv-templ-when-sg
      solver.setOption("sygus-inv-templ-when-sg", "true"); break;
    case 774: // --no-sygus-inv-templ-when-sg
      solver.setOption("sygus-inv-templ-when-sg", "false"); break;
    case 775: // --sygus-min-grammar
      solver.setOption("sygus-min-grammar", "true"); break;
    case 776: // --no-sygus-min-grammar
      solver.setOption("sygus-min-grammar", "false"); break;
    case 777: // --sygus-out
      solver.setOption("sygus-out", optionarg); break;
    case 778: // --sygus-pbe
      solver.setOption("sygus-pbe", "true"); break;
    case 779: // --no-sygus-pbe
      solver.setOption("sygus-pbe", "false"); break;
    case 780: // --sygus-pbe-multi-fair
      solver.setOption("sygus-pbe-multi-fair", "true"); break;
    case 781: // --no-sygus-pbe-multi-fair
      solver.setOption("sygus-pbe-multi-fair", "false"); break;
    case 782: // --sygus-pbe-multi-fair-diff
      solver.setOption("sygus-pbe-multi-fair-diff", optionarg); break;
    case 783: // --sygus-qe-preproc
      solver.setOption("sygus-qe-preproc", "true"); break;
    case 784: // --no-sygus-qe-preproc
      solver.setOption("sygus-qe-preproc", "false"); break;
    case 785: // --sygus-query-gen
      solver.setOption("sygus-query-gen", optionarg); break;
    case 786: // --sygus-query-gen-dump-files
      solver.setOption("sygus-query-gen-dump-files", optionarg); break;
    case 787: // --sygus-query-gen-thresh
      solver.setOption("sygus-query-gen-thresh", optionarg); break;
    case 788: // --sygus-rec-fun
      solver.setOption("sygus-rec-fun", "true"); break;
    case 789: // --no-sygus-rec-fun
      solver.setOption("sygus-rec-fun", "false"); break;
    case 790: // --sygus-rec-fun-eval-limit
      solver.setOption("sygus-rec-fun-eval-limit", optionarg); break;
    case 791: // --sygus-repair-const
      solver.setOption("sygus-repair-const", "true"); break;
    case 792: // --no-sygus-repair-const
      solver.setOption("sygus-repair-const", "false"); break;
    case 793: // --sygus-repair-const-timeout
      solver.setOption("sygus-repair-const-timeout", optionarg); break;
    case 794: // --sygus-rr-synth
      solver.setOption("sygus-rr-synth", "true"); break;
    case 795: // --no-sygus-rr-synth
      solver.setOption("sygus-rr-synth", "false"); break;
    case 796: // --sygus-rr-synth-accel
      solver.setOption("sygus-rr-synth-accel", "true"); break;
    case 797: // --no-sygus-rr-synth-accel
      solver.setOption("sygus-rr-synth-accel", "false"); break;
    case 798: // --sygus-rr-synth-check
      solver.setOption("sygus-rr-synth-check", "true"); break;
    case 799: // --no-sygus-rr-synth-check
      solver.setOption("sygus-rr-synth-check", "false"); break;
    case 800: // --sygus-rr-synth-filter-cong
      solver.setOption("sygus-rr-synth-filter-cong", "true"); break;
    case 801: // --no-sygus-rr-synth-filter-cong
      solver.setOption("sygus-rr-synth-filter-cong", "false"); break;
    case 802: // --sygus-rr-synth-filter-match
      solver.setOption("sygus-rr-synth-filter-match", "true"); break;
    case 803: // --no-sygus-rr-synth-filter-match
      solver.setOption("sygus-rr-synth-filter-match", "false"); break;
    case 804: // --sygus-rr-synth-filter-nl
      solver.setOption("sygus-rr-synth-filter-nl", "true"); break;
    case 805: // --no-sygus-rr-synth-filter-nl
      solver.setOption("sygus-rr-synth-filter-nl", "false"); break;
    case 806: // --sygus-rr-synth-filter-order
      solver.setOption("sygus-rr-synth-filter-order", "true"); break;
    case 807: // --no-sygus-rr-synth-filter-order
      solver.setOption("sygus-rr-synth-filter-order", "false"); break;
    case 808: // --sygus-rr-synth-input
      solver.setOption("sygus-rr-synth-input", "true"); break;
    case 809: // --no-sygus-rr-synth-input
      solver.setOption("sygus-rr-synth-input", "false"); break;
    case 810: // --sygus-rr-synth-input-nvars
      solver.setOption("sygus-rr-synth-input-nvars", optionarg); break;
    case 811: // --sygus-rr-synth-input-use-bool
      solver.setOption("sygus-rr-synth-input-use-bool", "true"); break;
    case 812: // --no-sygus-rr-synth-input-use-bool
      solver.setOption("sygus-rr-synth-input-use-bool", "false"); break;
    case 813: // --sygus-rr-synth-rec
      solver.setOption("sygus-rr-synth-rec", "true"); break;
    case 814: // --no-sygus-rr-synth-rec
      solver.setOption("sygus-rr-synth-rec", "false"); break;
    case 815: // --sygus-rr-verify
      solver.setOption("sygus-rr-verify", "true"); break;
    case 816: // --no-sygus-rr-verify
      solver.setOption("sygus-rr-verify", "false"); break;
    case 817: // --sygus-sample-fp-uniform
      solver.setOption("sygus-sample-fp-uniform", "true"); break;
    case 818: // --no-sygus-sample-fp-uniform
      solver.setOption("sygus-sample-fp-uniform", "false"); break;
    case 819: // --sygus-sample-grammar
      solver.setOption("sygus-sample-grammar", "true"); break;
    case 820: // --no-sygus-sample-grammar
      solver.setOption("sygus-sample-grammar", "false"); break;
    case 821: // --sygus-samples
      solver.setOption("sygus-samples", optionarg); break;
    case 822: // --sygus-si
      solver.setOption("sygus-si", optionarg); break;
    case 823: // --sygus-si-abort
      solver.setOption("sygus-si-abort", "true"); break;
    case 824: // --no-sygus-si-abort
      solver.setOption("sygus-si-abort", "false"); break;
    case 825: // --sygus-si-rcons
      solver.setOption("sygus-si-rcons", optionarg); break;
    case 826: // --sygus-si-rcons-limit
      solver.setOption("sygus-si-rcons-limit", optionarg); break;
    case 827: // --sygus-stream
      solver.setOption("sygus-stream", "true"); break;
    case 828: // --no-sygus-stream
      solver.setOption("sygus-stream", "false"); break;
    case 829: // --sygus-unif-cond-independent-no-repeat-sol
      solver.setOption("sygus-unif-cond-independent-no-repeat-sol", "true"); break;
    case 830: // --no-sygus-unif-cond-independent-no-repeat-sol
      solver.setOption("sygus-unif-cond-independent-no-repeat-sol", "false"); break;
    case 831: // --sygus-unif-pi
      solver.setOption("sygus-unif-pi", optionarg); break;
    case 832: // --sygus-unif-shuffle-cond
      solver.setOption("sygus-unif-shuffle-cond", "true"); break;
    case 833: // --no-sygus-unif-shuffle-cond
      solver.setOption("sygus-unif-shuffle-cond", "false"); break;
    case 834: // --sygus-verify-inst-max-rounds
      solver.setOption("sygus-verify-inst-max-rounds", optionarg); break;
    case 835: // --sygus-verify-timeout
      solver.setOption("sygus-verify-timeout", optionarg); break;
    case 836: // --term-db-cd
      solver.setOption("term-db-cd", "true"); break;
    case 837: // --no-term-db-cd
      solver.setOption("term-db-cd", "false"); break;
    case 838: // --term-db-mode
      solver.setOption("term-db-mode", optionarg); break;
    case 839: // --trigger-active-sel
      solver.setOption("trigger-active-sel", optionarg); break;
    case 840: // --trigger-sel
      solver.setOption("trigger-sel", optionarg); break;
    case 841: // --user-pat
      solver.setOption("user-pat", optionarg); break;
    case 842: // --user-pool
      solver.setOption("user-pool", optionarg); break;
    case 843: // --var-elim-quant
      solver.setOption("var-elim-quant", "true"); break;
    case 844: // --no-var-elim-quant
      solver.setOption("var-elim-quant", "false"); break;
    case 845: // --var-ineq-elim-quant
      solver.setOption("var-ineq-elim-quant", "true"); break;
    case 846: // --no-var-ineq-elim-quant
      solver.setOption("var-ineq-elim-quant", "false"); break;
    case 847: // --sep-min-refine
      solver.setOption("sep-min-refine", "true"); break;
    case 848: // --no-sep-min-refine
      solver.setOption("sep-min-refine", "false"); break;
    case 849: // --sep-pre-skolem-emp
      solver.setOption("sep-pre-skolem-emp", "true"); break;
    case 850: // --no-sep-pre-skolem-emp
      solver.setOption("sep-pre-skolem-emp", "false"); break;
    case 851: // --sets-ext
      solver.setOption("sets-ext", "true"); break;
    case 852: // --no-sets-ext
      solver.setOption("sets-ext", "false"); break;
    case 853: // --sets-infer-as-lemmas
      solver.setOption("sets-infer-as-lemmas", "true"); break;
    case 854: // --no-sets-infer-as-lemmas
      solver.setOption("sets-infer-as-lemmas", "false"); break;
    case 855: // --sets-proxy-lemmas
      solver.setOption("sets-proxy-lemmas", "true"); break;
    case 856: // --no-sets-proxy-lemmas
      solver.setOption("sets-proxy-lemmas", "false"); break;
    case 857: // --abstract-values
      solver.setOption("abstract-values", "true"); break;
    case 858: // --no-abstract-values
      solver.setOption("abstract-values", "false"); break;
    case 859: // --ackermann
      solver.setOption("ackermann", "true"); break;
    case 860: // --no-ackermann
      solver.setOption("ackermann", "false"); break;
    case 861: // --bv-to-int-use-pow2
      solver.setOption("bv-to-int-use-pow2", "true"); break;
    case 862: // --no-bv-to-int-use-pow2
      solver.setOption("bv-to-int-use-pow2", "false"); break;
    case 863: // --bvand-integer-granularity
      solver.setOption("bvand-integer-granularity", optionarg); break;
    case 864: // --check-abducts
      solver.setOption("check-abducts", "true"); break;
    case 865: // --no-check-abducts
      solver.setOption("check-abducts", "false"); break;
    case 866: // --check-interpolants
      solver.setOption("check-interpolants", "true"); break;
    case 867: // --no-check-interpolants
      solver.setOption("check-interpolants", "false"); break;
    case 868: // --check-models
      solver.setOption("check-models", "true"); break;
    case 869: // --no-check-models
      solver.setOption("check-models", "false"); break;
    case 870: // --check-proofs
      solver.setOption("check-proofs", "true"); break;
    case 871: // --no-check-proofs
      solver.setOption("check-proofs", "false"); break;
    case 872: // --check-synth-sol
      solver.setOption("check-synth-sol", "true"); break;
    case 873: // --no-check-synth-sol
      solver.setOption("check-synth-sol", "false"); break;
    case 874: // --check-unsat-cores
      solver.setOption("check-unsat-cores", "true"); break;
    case 875: // --no-check-unsat-cores
      solver.setOption("check-unsat-cores", "false"); break;
    case 876: // --debug-check-models
      solver.setOption("debug-check-models", "true"); break;
    case 877: // --no-debug-check-models
      solver.setOption("debug-check-models", "false"); break;
    case 878: // --deep-restart
      solver.setOption("deep-restart", optionarg); break;
    case 879: // --deep-restart-factor
      solver.setOption("deep-restart-factor", optionarg); break;
    case 880: // --difficulty-mode
      solver.setOption("difficulty-mode", optionarg); break;
    case 881: // --early-ite-removal
      solver.setOption("early-ite-removal", "true"); break;
    case 882: // --no-early-ite-removal
      solver.setOption("early-ite-removal", "false"); break;
    case 883: // --ext-rew-prep
      solver.setOption("ext-rew-prep", optionarg); break;
    case 884: // --foreign-theory-rewrite
      solver.setOption("foreign-theory-rewrite", "true"); break;
    case 885: // --no-foreign-theory-rewrite
      solver.setOption("foreign-theory-rewrite", "false"); break;
    case 886: // --iand-mode
      solver.setOption("iand-mode", optionarg); break;
    case 887: // --interpolants-mode
      solver.setOption("interpolants-mode", optionarg); break;
    case 888: // --ite-simp
      solver.setOption("ite-simp", "true"); break;
    case 889: // --no-ite-simp
      solver.setOption("ite-simp", "false"); break;
    case 890: // --learned-rewrite
      solver.setOption("learned-rewrite", "true"); break;
    case 891: // --no-learned-rewrite
      solver.setOption("learned-rewrite", "false"); break;
    case 892: // --minimal-unsat-cores
      solver.setOption("minimal-unsat-cores", "true"); break;
    case 893: // --no-minimal-unsat-cores
      solver.setOption("minimal-unsat-cores", "false"); break;
    case 894: // --model-cores
      solver.setOption("model-cores", optionarg); break;
    case 895: // --model-var-elim-uneval
      solver.setOption("model-var-elim-uneval", "true"); break;
    case 896: // --no-model-var-elim-uneval
      solver.setOption("model-var-elim-uneval", "false"); break;
    case 897: // --on-repeat-ite-simp
      solver.setOption("on-repeat-ite-simp", "true"); break;
    case 898: // --no-on-repeat-ite-simp
      solver.setOption("on-repeat-ite-simp", "false"); break;
    case 899: // --print-unsat-cores-full
      solver.setOption("print-unsat-cores-full", "true"); break;
    case 900: // --no-print-unsat-cores-full
      solver.setOption("print-unsat-cores-full", "false"); break;
    case 901: // --produce-abducts
      solver.setOption("produce-abducts", "true"); break;
    case 902: // --no-produce-abducts
      solver.setOption("produce-abducts", "false"); break;
    case 903: // --produce-assertions
    case 904: // --interactive-mode
      solver.setOption("produce-assertions", "true"); break;
    case 905: // --no-produce-assertions
    case 906: // --no-interactive-mode
      solver.setOption("produce-assertions", "false"); break;
    case 907: // --produce-assignments
      solver.setOption("produce-assignments", "true"); break;
    case 908: // --no-produce-assignments
      solver.setOption("produce-assignments", "false"); break;
    case 909: // --produce-difficulty
      solver.setOption("produce-difficulty", "true"); break;
    case 910: // --no-produce-difficulty
      solver.setOption("produce-difficulty", "false"); break;
    case 911: // --produce-interpolants
      solver.setOption("produce-interpolants", "true"); break;
    case 912: // --no-produce-interpolants
      solver.setOption("produce-interpolants", "false"); break;
    case 913: // --produce-learned-literals
      solver.setOption("produce-learned-literals", "true"); break;
    case 914: // --no-produce-learned-literals
      solver.setOption("produce-learned-literals", "false"); break;
    case 'm': // -m
    case 915: // --produce-models
      solver.setOption("produce-models", "true"); break;
    case 916: // --no-produce-models
      solver.setOption("produce-models", "false"); break;
    case 917: // --produce-proofs
      solver.setOption("produce-proofs", "true"); break;
    case 918: // --no-produce-proofs
      solver.setOption("produce-proofs", "false"); break;
    case 919: // --produce-unsat-assumptions
      solver.setOption("produce-unsat-assumptions", "true"); break;
    case 920: // --no-produce-unsat-assumptions
      solver.setOption("produce-unsat-assumptions", "false"); break;
    case 921: // --produce-unsat-cores
      solver.setOption("produce-unsat-cores", "true"); break;
    case 922: // --no-produce-unsat-cores
      solver.setOption("produce-unsat-cores", "false"); break;
    case 923: // --proof-mode
      solver.setOption("proof-mode", optionarg); break;
    case 924: // --repeat-simp
      solver.setOption("repeat-simp", "true"); break;
    case 925: // --no-repeat-simp
      solver.setOption("repeat-simp", "false"); break;
    case 926: // --simp-ite-compress
      solver.setOption("simp-ite-compress", "true"); break;
    case 927: // --no-simp-ite-compress
      solver.setOption("simp-ite-compress", "false"); break;
    case 928: // --simp-with-care
      solver.setOption("simp-with-care", "true"); break;
    case 929: // --no-simp-with-care
      solver.setOption("simp-with-care", "false"); break;
    case 930: // --simplification
    case 931: // --simplification-mode
      solver.setOption("simplification", optionarg); break;
    case 932: // --simplification-bcp
      solver.setOption("simplification-bcp", "true"); break;
    case 933: // --no-simplification-bcp
      solver.setOption("simplification-bcp", "false"); break;
    case 934: // --solve-bv-as-int
      solver.setOption("solve-bv-as-int", optionarg); break;
    case 935: // --solve-int-as-bv
      solver.setOption("solve-int-as-bv", optionarg); break;
    case 936: // --solve-real-as-int
      solver.setOption("solve-real-as-int", "true"); break;
    case 937: // --no-solve-real-as-int
      solver.setOption("solve-real-as-int", "false"); break;
    case 938: // --sort-inference
      solver.setOption("sort-inference", "true"); break;
    case 939: // --no-sort-inference
      solver.setOption("sort-inference", "false"); break;
    case 940: // --static-learning
      solver.setOption("static-learning", "true"); break;
    case 941: // --no-static-learning
      solver.setOption("static-learning", "false"); break;
    case 942: // --unconstrained-simp
      solver.setOption("unconstrained-simp", "true"); break;
    case 943: // --no-unconstrained-simp
      solver.setOption("unconstrained-simp", "false"); break;
    case 944: // --unsat-cores-mode
      solver.setOption("unsat-cores-mode", optionarg); break;
    case 945: // --re-elim
      solver.setOption("re-elim", optionarg); break;
    case 946: // --re-inter-mode
      solver.setOption("re-inter-mode", optionarg); break;
    case 947: // --seq-array
      solver.setOption("seq-array", optionarg); break;
    case 948: // --strings-alpha-card
      solver.setOption("strings-alpha-card", optionarg); break;
    case 949: // --strings-check-entail-len
      solver.setOption("strings-check-entail-len", "true"); break;
    case 950: // --no-strings-check-entail-len
      solver.setOption("strings-check-entail-len", "false"); break;
    case 951: // --strings-code-elim
      solver.setOption("strings-code-elim", "true"); break;
    case 952: // --no-strings-code-elim
      solver.setOption("strings-code-elim", "false"); break;
    case 953: // --strings-deq-ext
      solver.setOption("strings-deq-ext", "true"); break;
    case 954: // --no-strings-deq-ext
      solver.setOption("strings-deq-ext", "false"); break;
    case 955: // --strings-eager-eval
      solver.setOption("strings-eager-eval", "true"); break;
    case 956: // --no-strings-eager-eval
      solver.setOption("strings-eager-eval", "false"); break;
    case 957: // --strings-eager-len-re
      solver.setOption("strings-eager-len-re", "true"); break;
    case 958: // --no-strings-eager-len-re
      solver.setOption("strings-eager-len-re", "false"); break;
    case 959: // --strings-eager-reg
      solver.setOption("strings-eager-reg", "true"); break;
    case 960: // --no-strings-eager-reg
      solver.setOption("strings-eager-reg", "false"); break;
    case 961: // --strings-eager-solver
      solver.setOption("strings-eager-solver", "true"); break;
    case 962: // --no-strings-eager-solver
      solver.setOption("strings-eager-solver", "false"); break;
    case 963: // --strings-exp
      solver.setOption("strings-exp", "true"); break;
    case 964: // --no-strings-exp
      solver.setOption("strings-exp", "false"); break;
    case 965: // --strings-ff
      solver.setOption("strings-ff", "true"); break;
    case 966: // --no-strings-ff
      solver.setOption("strings-ff", "false"); break;
    case 967: // --strings-fmf
      solver.setOption("strings-fmf", "true"); break;
    case 968: // --no-strings-fmf
      solver.setOption("strings-fmf", "false"); break;
    case 969: // --strings-infer-as-lemmas
      solver.setOption("strings-infer-as-lemmas", "true"); break;
    case 970: // --no-strings-infer-as-lemmas
      solver.setOption("strings-infer-as-lemmas", "false"); break;
    case 971: // --strings-infer-sym
      solver.setOption("strings-infer-sym", "true"); break;
    case 972: // --no-strings-infer-sym
      solver.setOption("strings-infer-sym", "false"); break;
    case 973: // --strings-lazy-pp
      solver.setOption("strings-lazy-pp", "true"); break;
    case 974: // --no-strings-lazy-pp
      solver.setOption("strings-lazy-pp", "false"); break;
    case 975: // --strings-len-norm
      solver.setOption("strings-len-norm", "true"); break;
    case 976: // --no-strings-len-norm
      solver.setOption("strings-len-norm", "false"); break;
    case 977: // --strings-mbr
      solver.setOption("strings-mbr", "true"); break;
    case 978: // --no-strings-mbr
      solver.setOption("strings-mbr", "false"); break;
    case 979: // --strings-model-max-len
      solver.setOption("strings-model-max-len", optionarg); break;
    case 980: // --strings-process-loop-mode
      solver.setOption("strings-process-loop-mode", optionarg); break;
    case 981: // --strings-re-posc-eager
      solver.setOption("strings-re-posc-eager", "true"); break;
    case 982: // --no-strings-re-posc-eager
      solver.setOption("strings-re-posc-eager", "false"); break;
    case 983: // --strings-regexp-inclusion
      solver.setOption("strings-regexp-inclusion", "true"); break;
    case 984: // --no-strings-regexp-inclusion
      solver.setOption("strings-regexp-inclusion", "false"); break;
    case 985: // --strings-rexplain-lemmas
      solver.setOption("strings-rexplain-lemmas", "true"); break;
    case 986: // --no-strings-rexplain-lemmas
      solver.setOption("strings-rexplain-lemmas", "false"); break;
    case 987: // --assign-function-values
      solver.setOption("assign-function-values", "true"); break;
    case 988: // --no-assign-function-values
      solver.setOption("assign-function-values", "false"); break;
    case 989: // --condense-function-values
      solver.setOption("condense-function-values", "true"); break;
    case 990: // --no-condense-function-values
      solver.setOption("condense-function-values", "false"); break;
    case 991: // --ee-mode
      solver.setOption("ee-mode", optionarg); break;
    case 992: // --relevance-filter
      solver.setOption("relevance-filter", "true"); break;
    case 993: // --no-relevance-filter
      solver.setOption("relevance-filter", "false"); break;
    case 994: // --tc-mode
      solver.setOption("tc-mode", optionarg); break;
    case 995: // --theoryof-mode
      solver.setOption("theoryof-mode", optionarg); break;
    case 996: // --eager-arith-bv-conv
      solver.setOption("eager-arith-bv-conv", "true"); break;
    case 997: // --no-eager-arith-bv-conv
      solver.setOption("eager-arith-bv-conv", "false"); break;
    case 998: // --symmetry-breaker
      solver.setOption("symmetry-breaker", "true"); break;
    case 999: // --no-symmetry-breaker
      solver.setOption("symmetry-breaker", "false"); break;
    case 1000: // --uf-ho-ext
      solver.setOption("uf-ho-ext", "true"); break;
    case 1001: // --no-uf-ho-ext
      solver.setOption("uf-ho-ext", "false"); break;
    case 1002: // --uf-lazy-ll
      solver.setOption("uf-lazy-ll", "true"); break;
    case 1003: // --no-uf-lazy-ll
      solver.setOption("uf-lazy-ll", "false"); break;
    case 1004: // --uf-ss
      solver.setOption("uf-ss", optionarg); break;
    case 1005: // --uf-ss-abort-card
      solver.setOption("uf-ss-abort-card", optionarg); break;
    case 1006: // --uf-ss-fair
      solver.setOption("uf-ss-fair", "true"); break;
    case 1007: // --no-uf-ss-fair
      solver.setOption("uf-ss-fair", "false"); break;
    case 1008: // --uf-ss-fair-monotone
      solver.setOption("uf-ss-fair-monotone", "true"); break;
    case 1009: // --no-uf-ss-fair-monotone
      solver.setOption("uf-ss-fair-monotone", "false"); break;
// clang-format on

    case ':' :
      // This can be a long or short option, and the way to get at the
      // name of it is different.
      throw OptionException(std::string("option `") + option
                            + "' missing its required argument");
    case '?':
    default:
      throw OptionException(std::string("can't understand option `") + option
                            + "'" + suggestCommandLineOptions(option));
    }
  }

  Trace("options") << "got " << nonoptions.size() << " non-option arguments."
                   << std::endl;
}

/**
 * Parse argc/argv and put the result into a cvc5::internal::Options.
 * The return value is what's left of the command line (that is, the
 * non-option arguments).
 *
 * Throws OptionException on failures.
 */
std::vector<std::string> parse(cvc5::Solver& solver,
                               int argc,
                               char* argv[],
                               std::string& binaryName)
{
  Assert(argv != nullptr);

  const char* progName = argv[0];

  // To debug options parsing, you may prefer to simply uncomment this
  // and recompile. Debug flags have not been parsed yet so these have
  // not been set.
  // TraceChannel.on("options");

  Trace("options") << "argv == " << argv << std::endl;

  // Find the base name of the program.
  const char* x = strrchr(progName, '/');
  if (x != nullptr)
  {
    progName = x + 1;
  }
  binaryName = std::string(progName);

  std::vector<std::string> nonoptions;
  parseInternal(solver, argc, argv, nonoptions);
  if (TraceIsOn("options"))
  {
    for (const auto& no : nonoptions)
    {
      Trace("options") << "nonoptions " << no << std::endl;
    }
  }

  return nonoptions;
}

}  // namespace cvc5::main
