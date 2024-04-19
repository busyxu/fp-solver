/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2010-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This header file was automatically generated by:
 *
 *     ../../../src/expr/mkkind /home/aaa/fp-solver/cvc5/src/expr/type_properties_template.cpp /home/aaa/fp-solver/cvc5/src/theory/builtin/kinds /home/aaa/fp-solver/cvc5/src/theory/booleans/kinds /home/aaa/fp-solver/cvc5/src/theory/uf/kinds /home/aaa/fp-solver/cvc5/src/theory/arith/kinds /home/aaa/fp-solver/cvc5/src/theory/bv/kinds /home/aaa/fp-solver/cvc5/src/theory/ff/kinds /home/aaa/fp-solver/cvc5/src/theory/fp/kinds /home/aaa/fp-solver/cvc5/src/theory/arrays/kinds /home/aaa/fp-solver/cvc5/src/theory/datatypes/kinds /home/aaa/fp-solver/cvc5/src/theory/sep/kinds /home/aaa/fp-solver/cvc5/src/theory/sets/kinds /home/aaa/fp-solver/cvc5/src/theory/bags/kinds /home/aaa/fp-solver/cvc5/src/theory/strings/kinds /home/aaa/fp-solver/cvc5/src/theory/quantifiers/kinds
 *
 * for the cvc5 project.
 */

/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */

/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */

/* Edit the template file instead:                     */
/* /home/aaa/fp-solver/cvc5/src/expr/type_properties_template.cpp */

/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Template for the Type properties source file.
 */

#include "expr/type_properties.h"

namespace cvc5::internal {
namespace kind {

Node mkGroundTerm(TypeConstant tc)
{
  switch (tc)
  {
    // clang-format off

  case BUILTIN_OPERATOR_TYPE: Unhandled() << tc;

  case SEXPR_TYPE: Unhandled() << tc;

  case BOOLEAN_TYPE: return NodeManager::currentNM()->mkConst(false);

  case REAL_TYPE: return NodeManager::currentNM()->mkConstReal(Rational(0));

  case INTEGER_TYPE: return NodeManager::currentNM()->mkConstInt(Rational(0));

  case ROUNDINGMODE_TYPE: return NodeManager::currentNM()->mkConst<RoundingMode>(RoundingMode());

  case STRING_TYPE: return NodeManager::currentNM()->mkConst(::cvc5::internal::String());

  case REGEXP_TYPE: return NodeManager::currentNM()->mkNode(REGEXP_NONE);

  case BOUND_VAR_LIST_TYPE: Unhandled() << tc;

  case INST_PATTERN_TYPE: Unhandled() << tc;

  case INST_PATTERN_LIST_TYPE: Unhandled() << tc;

      // clang-format on
    default:
      InternalError() << "No ground term known for type constant: " << tc;
  }
}

Node mkGroundTerm(TypeNode typeNode)
{
  AssertArgument(!typeNode.isNull(), typeNode);
  switch (Kind k = typeNode.getKind())
  {
    case TYPE_CONSTANT:
      return mkGroundTerm(typeNode.getConst<TypeConstant>());
      // clang-format off

  case SORT_TYPE: return ::cvc5::internal::theory::builtin::SortProperties::mkGroundTerm(typeNode);

  case INSTANTIATED_SORT_TYPE: return ::cvc5::internal::theory::builtin::SortProperties::mkGroundTerm(typeNode);

  case FUNCTION_TYPE: return ::cvc5::internal::theory::uf::FunctionProperties::mkGroundTerm(typeNode);

  case BITVECTOR_TYPE: return (*cvc5::internal::theory::TypeEnumerator(typeNode));

  case FINITE_FIELD_TYPE: return (*cvc5::internal::theory::TypeEnumerator(typeNode));

  case FLOATINGPOINT_TYPE: return (*cvc5::internal::theory::TypeEnumerator(typeNode));

  case ARRAY_TYPE: return ::cvc5::internal::theory::arrays::ArraysProperties::mkGroundTerm(typeNode);

  case DATATYPE_TYPE: return typeNode.getDType().mkGroundTerm(typeNode);

  case PARAMETRIC_DATATYPE: return typeNode.getDType().mkGroundTerm(typeNode);

  case TUPLE_TYPE: return typeNode.getDType().mkGroundTerm(typeNode);

  case SET_TYPE: return ::cvc5::internal::theory::sets::SetsProperties::mkGroundTerm(typeNode);

  case BAG_TYPE: return ::cvc5::internal::theory::bags::BagsProperties::mkGroundTerm(typeNode);

  case SEQUENCE_TYPE: return ::cvc5::internal::theory::strings::SequenceProperties::mkGroundTerm(typeNode);

      // clang-format on
    default:
      InternalError() << "A theory kinds file did not provide a ground term "
                      << "or ground term computer for type:\n"
                      << typeNode << "\nof kind " << k;
  }
}

}  // namespace kind
}  // namespace cvc5::internal
