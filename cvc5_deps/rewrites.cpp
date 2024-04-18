/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generated rewrites
 */

#include "expr/node.h"
#include "expr/node_manager.h"
#include "proof/proof_checker.h"
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrites.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

void addRules(RewriteDb& db)
{
  NodeManager* nm = NodeManager::currentNM();

  // Variables
  Node t1 = nm->mkBoundVar("t1", nm->booleanType());
  Node t2 = nm->mkBoundVar("t2", nm->booleanType());
  Node s3 = nm->mkBoundVar("s3", nm->booleanType());
  Node t4 = nm->mkBoundVar("t4", nm->booleanType());
  Node t5 = nm->mkBoundVar("t5", nm->booleanType());
  Node t6 = nm->mkBoundVar("t6", nm->booleanType());
  Node t7 = nm->mkBoundVar("t7", nm->booleanType());
  Node t8 = nm->mkBoundVar("t8", nm->booleanType());
  Node t9 = nm->mkBoundVar("t9", nm->booleanType());
  Node t10 = nm->mkBoundVar("t10", nm->booleanType());
  Node xs11 = nm->mkBoundVar("xs11", nm->booleanType());
  expr::markListVar(xs11);
  Node ys12 = nm->mkBoundVar("ys12", nm->booleanType());
  expr::markListVar(ys12);
  Node xs13 = nm->mkBoundVar("xs13", nm->booleanType());
  expr::markListVar(xs13);
  Node ys14 = nm->mkBoundVar("ys14", nm->booleanType());
  expr::markListVar(ys14);
  Node xs15 = nm->mkBoundVar("xs15", nm->booleanType());
  expr::markListVar(xs15);
  Node b16 = nm->mkBoundVar("b16", nm->booleanType());
  Node ys17 = nm->mkBoundVar("ys17", nm->booleanType());
  expr::markListVar(ys17);
  Node zs18 = nm->mkBoundVar("zs18", nm->booleanType());
  expr::markListVar(zs18);
  Node xs19 = nm->mkBoundVar("xs19", nm->booleanType());
  expr::markListVar(xs19);
  Node b20 = nm->mkBoundVar("b20", nm->booleanType());
  Node ys21 = nm->mkBoundVar("ys21", nm->booleanType());
  expr::markListVar(ys21);
  Node zs22 = nm->mkBoundVar("zs22", nm->booleanType());
  expr::markListVar(zs22);
  Node xs23 = nm->mkBoundVar("xs23", nm->booleanType());
  expr::markListVar(xs23);
  Node ys24 = nm->mkBoundVar("ys24", nm->booleanType());
  expr::markListVar(ys24);
  Node xs25 = nm->mkBoundVar("xs25", nm->booleanType());
  expr::markListVar(xs25);
  Node ys26 = nm->mkBoundVar("ys26", nm->booleanType());
  expr::markListVar(ys26);
  Node xs27 = nm->mkBoundVar("xs27", nm->booleanType());
  expr::markListVar(xs27);
  Node b28 = nm->mkBoundVar("b28", nm->booleanType());
  Node ys29 = nm->mkBoundVar("ys29", nm->booleanType());
  expr::markListVar(ys29);
  Node zs30 = nm->mkBoundVar("zs30", nm->booleanType());
  expr::markListVar(zs30);
  Node xs31 = nm->mkBoundVar("xs31", nm->booleanType());
  expr::markListVar(xs31);
  Node b32 = nm->mkBoundVar("b32", nm->booleanType());
  Node ys33 = nm->mkBoundVar("ys33", nm->booleanType());
  expr::markListVar(ys33);
  Node zs34 = nm->mkBoundVar("zs34", nm->booleanType());
  expr::markListVar(zs34);
  Node x35 = nm->mkBoundVar("x35", nm->booleanType());
  Node y36 = nm->mkBoundVar("y36", nm->booleanType());
  Node x37 = nm->mkBoundVar("x37", nm->booleanType());
  Node y38 = nm->mkBoundVar("y38", nm->booleanType());
  Node c39 = nm->mkBoundVar("c39", nm->booleanType());
  Node x40 = nm->mkBoundVar("x40", nm->booleanType());
  Node y41 = nm->mkBoundVar("y41", nm->booleanType());
  Node xs42 = nm->mkBoundVar("xs42", nm->booleanType());
  expr::markListVar(xs42);
  Node w43 = nm->mkBoundVar("w43", nm->booleanType());
  Node ys44 = nm->mkBoundVar("ys44", nm->booleanType());
  expr::markListVar(ys44);
  Node zs45 = nm->mkBoundVar("zs45", nm->booleanType());
  expr::markListVar(zs45);
  Node xs46 = nm->mkBoundVar("xs46", nm->booleanType());
  expr::markListVar(xs46);
  Node w47 = nm->mkBoundVar("w47", nm->booleanType());
  Node ys48 = nm->mkBoundVar("ys48", nm->booleanType());
  expr::markListVar(ys48);
  Node zs49 = nm->mkBoundVar("zs49", nm->booleanType());
  expr::markListVar(zs49);

  // Definitions
  Node e50 = nm->mkConst(true);
  Node e51 = nm->mkConst(false);

  // Rules

  {
    // from /home/yangxu/cvc5/src/theory/booleans/rewrites
    db.addRule(DslPfRule::BOOL_EQ_REFL,
               {t1},
               nm->mkNode(EQUAL, {t1, t1}),
               e50,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_EQ_SYMM,
               {t2, s3},
               nm->mkNode(EQUAL, {t2, s3}),
               nm->mkNode(EQUAL, {s3, t2}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_DOUBLE_NEG_ELIM,
               {t4},
               nm->mkNode(NOT, {nm->mkNode(NOT, {t4})}),
               t4,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_EQ_TRUE,
               {t5},
               nm->mkNode(EQUAL, {t5, e50}),
               t5,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_EQ_FALSE,
               {t6},
               nm->mkNode(EQUAL, {t6, e51}),
               nm->mkNode(NOT, {t6}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_IMPL_FALSE1,
               {t7},
               nm->mkNode(IMPLIES, {t7, e51}),
               nm->mkNode(NOT, {t7}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_IMPL_FALSE2,
               {t8},
               nm->mkNode(IMPLIES, {e51, t8}),
               e50,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_IMPL_TRUE1,
               {t9},
               nm->mkNode(IMPLIES, {t9, e50}),
               e50,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_IMPL_TRUE2,
               {t10},
               nm->mkNode(IMPLIES, {e50, t10}),
               t10,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_OR_TRUE,
               {xs11, ys12},
               nm->mkNode(OR, {xs11, e50, ys12}),
               e50,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_OR_FALSE,
               {xs13, ys14},
               nm->mkNode(OR, {xs13, e51, ys14}),
               nm->mkNode(OR, {xs13, ys14}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_OR_FLATTEN,
               {xs15, b16, ys17, zs18},
               nm->mkNode(OR, {xs15, nm->mkNode(OR, {b16, ys17}), zs18}),
               nm->mkNode(OR, {xs15, zs18, b16, ys17}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_OR_DUP,
               {xs19, b20, ys21, zs22},
               nm->mkNode(OR, {xs19, b20, ys21, b20, zs22}),
               nm->mkNode(OR, {xs19, b20, ys21, zs22}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_AND_TRUE,
               {xs23, ys24},
               nm->mkNode(AND, {xs23, e50, ys24}),
               nm->mkNode(AND, {xs23, ys24}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_AND_FALSE,
               {xs25, ys26},
               nm->mkNode(AND, {xs25, e51, ys26}),
               e51,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_AND_FLATTEN,
               {xs27, b28, ys29, zs30},
               nm->mkNode(AND, {xs27, nm->mkNode(AND, {b28, ys29}), zs30}),
               nm->mkNode(AND, {xs27, zs30, b28, ys29}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_AND_DUP,
               {xs31, b32, ys33, zs34},
               nm->mkNode(AND, {xs31, b32, ys33, b32, zs34}),
               nm->mkNode(AND, {xs31, b32, ys33, zs34}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_ITE_TRUE_COND,
               {x35, y36},
               nm->mkNode(ITE, {e50, x35, y36}),
               x35,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_ITE_FALSE_COND,
               {x37, y38},
               nm->mkNode(ITE, {e51, x37, y38}),
               y38,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_ITE_NOT_COND,
               {c39, x40, y41},
               nm->mkNode(ITE, {nm->mkNode(NOT, {c39}), x40, y41}),
               nm->mkNode(ITE, {c39, y41, x40}),
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_AND_CONF,
               {xs42, w43, ys44, zs45},
               nm->mkNode(AND, {xs42, w43, ys44, nm->mkNode(NOT, {w43}), zs45}),
               e51,
               e50,
               Node::null());
    db.addRule(DslPfRule::BOOL_OR_TAUT,
               {xs46, w47, ys48, zs49},
               nm->mkNode(OR, {xs46, w47, ys48, nm->mkNode(NOT, {w47}), zs49}),
               e50,
               e50,
               Node::null());
  }
}
const char* toString(DslPfRule drule)
{
  switch (drule)
  {
    case DslPfRule::FAIL: return "FAIL";
    case DslPfRule::REFL: return "REFL";
    case DslPfRule::EVAL: return "EVAL";
    case DslPfRule::BOOL_EQ_REFL: return "bool-eq-refl";
    case DslPfRule::BOOL_EQ_SYMM: return "bool-eq-symm";
    case DslPfRule::BOOL_DOUBLE_NEG_ELIM: return "bool-double-neg-elim";
    case DslPfRule::BOOL_EQ_TRUE: return "bool-eq-true";
    case DslPfRule::BOOL_EQ_FALSE: return "bool-eq-false";
    case DslPfRule::BOOL_IMPL_FALSE1: return "bool-impl-false1";
    case DslPfRule::BOOL_IMPL_FALSE2: return "bool-impl-false2";
    case DslPfRule::BOOL_IMPL_TRUE1: return "bool-impl-true1";
    case DslPfRule::BOOL_IMPL_TRUE2: return "bool-impl-true2";
    case DslPfRule::BOOL_OR_TRUE: return "bool-or-true";
    case DslPfRule::BOOL_OR_FALSE: return "bool-or-false";
    case DslPfRule::BOOL_OR_FLATTEN: return "bool-or-flatten";
    case DslPfRule::BOOL_OR_DUP: return "bool-or-dup";
    case DslPfRule::BOOL_AND_TRUE: return "bool-and-true";
    case DslPfRule::BOOL_AND_FALSE: return "bool-and-false";
    case DslPfRule::BOOL_AND_FLATTEN: return "bool-and-flatten";
    case DslPfRule::BOOL_AND_DUP: return "bool-and-dup";
    case DslPfRule::BOOL_ITE_TRUE_COND: return "bool-ite-true-cond";
    case DslPfRule::BOOL_ITE_FALSE_COND: return "bool-ite-false-cond";
    case DslPfRule::BOOL_ITE_NOT_COND: return "bool-ite-not-cond";
    case DslPfRule::BOOL_AND_CONF: return "bool-and-conf";
    case DslPfRule::BOOL_OR_TAUT: return "bool-or-taut";
    default: Unreachable();
  }
}

std::ostream& operator<<(std::ostream& out, DslPfRule drule)
{
  out << toString(drule);
  return out;
}

Node mkDslPfRuleNode(DslPfRule i)
{
  return NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(i)));
}

bool getDslPfRule(TNode n, DslPfRule& i)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<DslPfRule>(index);
  return true;
}

}  // namespace rewriter
}  // namespace cvc5::internal
