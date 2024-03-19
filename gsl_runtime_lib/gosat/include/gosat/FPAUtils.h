//===------------------------------------------------------------*- C++ -*-===//
//
// This file is distributed under MIT License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Copyright (c) 2017 University of Kaiserslautern.
//

#pragma once

#include "z3++.h"

// functions called by JIT engine

double fp64_dis(double a, double b);
double fp64_eq_dis(double a, double b);
double fp64_neq_dis(double a, double b);
double fp64_isnan(double a, double flag);
// add by zgf
double fp64_isinf(double a, double flag);
double FPCHECK_FADD_OVERFLOW(double left,double right);
double FPCHECK_FADD_UNDERFLOW(double left,double right);
double FPCHECK_FSUB_OVERFLOW(double left,double right);
double FPCHECK_FSUB_UNDERFLOW(double left,double right);
double FPCHECK_FMUL_OVERFLOW(double left,double right);
double FPCHECK_FMUL_UNDERFLOW(double left,double right);
double FPCHECK_FDIV_OVERFLOW(double left,double right);
double FPCHECK_FDIV_UNDERFLOW(double left,double right);
double FPCHECK_FDIV_INVALID(double left,double right);
double FPCHECK_FDIV_ZERO(double left,double right);

// end of functions

namespace gosat {
namespace fpa_util {

bool inline
isFloat32(const unsigned exponent, const unsigned significand) noexcept
{
    return (exponent == 8 && significand == 24);
}

bool inline
isFloat64(const unsigned exponent, const unsigned significand) noexcept
{
    return (exponent == 11 && significand == 53);
}


bool inline isFPVar(const z3::expr& expr) noexcept
{
    return (expr.num_args() == 0
            && expr.decl().decl_kind() == Z3_OP_UNINTERPRETED
            && expr.get_sort().sort_kind() == Z3_FLOATING_POINT_SORT);
}

// add by zgf
bool inline isBV32(const unsigned width) noexcept{ return width == 32; }
bool inline isBV64(const unsigned width) noexcept{ return width == 64; }
bool isBV32VarDecl(const z3::expr& expr) noexcept;
bool isBV64VarDecl(const z3::expr& expr) noexcept;

bool inline isBVVar(const z3::expr& expr) noexcept{
  return (expr.num_args() == 0
          && expr.decl().decl_kind() == Z3_OP_UNINTERPRETED
          && expr.get_sort().sort_kind() == Z3_BV_SORT);
}

bool isNonLinearFPExpr(const z3::expr& expr) noexcept;

bool isFloat32VarDecl(const z3::expr& expr) noexcept;

bool isFloat64VarDecl(const z3::expr& expr) noexcept;

bool isRoundingModeApp(const z3::expr expr) noexcept;

bool isBoolExpr(const z3::expr& expr) noexcept;

/**
 *
 * @param expr
 * @return float value of expression
 * @pre isFloat32
 */
float toFloat32(const z3::expr& expr) noexcept;

/**
 *
 * @param exp
 * @return double value of expression
 * @pre isFloat64
 */
double toFloat64(const z3::expr& expr) noexcept;

}
}
