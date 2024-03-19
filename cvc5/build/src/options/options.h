/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Morgan Deters
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

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_H
#define CVC5__OPTIONS__OPTIONS_H

#include <cvc5/cvc5_export.h>

#include <iosfwd>
#include <memory>
#include <string>
#include <vector>

namespace cvc5::internal {
namespace options {
  class OptionsHandler;
// clang-format off
  struct HolderARITH; // include "options/arith_options.h" if this is an incomplete type
  struct HolderARRAYS; // include "options/arrays_options.h" if this is an incomplete type
  struct HolderBASE; // include "options/base_options.h" if this is an incomplete type
  struct HolderBOOLEANS; // include "options/booleans_options.h" if this is an incomplete type
  struct HolderBUILTIN; // include "options/builtin_options.h" if this is an incomplete type
  struct HolderBV; // include "options/bv_options.h" if this is an incomplete type
  struct HolderDATATYPES; // include "options/datatypes_options.h" if this is an incomplete type
  struct HolderDECISION; // include "options/decision_options.h" if this is an incomplete type
  struct HolderEXPR; // include "options/expr_options.h" if this is an incomplete type
  struct HolderFF; // include "options/ff_options.h" if this is an incomplete type
  struct HolderFP; // include "options/fp_options.h" if this is an incomplete type
  struct HolderDRIVER; // include "options/main_options.h" if this is an incomplete type
  struct HolderPARALLEL; // include "options/parallel_options.h" if this is an incomplete type
  struct HolderPARSER; // include "options/parser_options.h" if this is an incomplete type
  struct HolderPRINTER; // include "options/printer_options.h" if this is an incomplete type
  struct HolderPROOF; // include "options/proof_options.h" if this is an incomplete type
  struct HolderPROP; // include "options/prop_options.h" if this is an incomplete type
  struct HolderQUANTIFIERS; // include "options/quantifiers_options.h" if this is an incomplete type
  struct HolderSEP; // include "options/sep_options.h" if this is an incomplete type
  struct HolderSETS; // include "options/sets_options.h" if this is an incomplete type
  struct HolderSMT; // include "options/smt_options.h" if this is an incomplete type
  struct HolderSTRINGS; // include "options/strings_options.h" if this is an incomplete type
  struct HolderTHEORY; // include "options/theory_options.h" if this is an incomplete type
  struct HolderUF; // include "options/uf_options.h" if this is an incomplete type
// clang-format on
}  // namespace options

class OptionsListener;

class CVC5_EXPORT Options
{
  public:
  /**
   * Options cannot be copied as they are given an explicit list of
   * Listeners to respond to.
   */
  Options(const Options& options) = delete;

  /**
   * Options cannot be assigned as they are given an explicit list of
   * Listeners to respond to.
   */
  Options& operator=(const Options& options) = delete;

  Options();
  ~Options();

  options::OptionsHandler& handler() const {
    return *d_handler;
  }

  /**
   * Copies the value of the options stored in OptionsHolder into the current
   * Options object.
   */
  void copyValues(const Options& options);

 private:

// clang-format off
    std::unique_ptr<options::HolderARITH> d_arith;
    std::unique_ptr<options::HolderARRAYS> d_arrays;
    std::unique_ptr<options::HolderBASE> d_base;
    std::unique_ptr<options::HolderBOOLEANS> d_booleans;
    std::unique_ptr<options::HolderBUILTIN> d_builtin;
    std::unique_ptr<options::HolderBV> d_bv;
    std::unique_ptr<options::HolderDATATYPES> d_datatypes;
    std::unique_ptr<options::HolderDECISION> d_decision;
    std::unique_ptr<options::HolderEXPR> d_expr;
    std::unique_ptr<options::HolderFF> d_ff;
    std::unique_ptr<options::HolderFP> d_fp;
    std::unique_ptr<options::HolderDRIVER> d_driver;
    std::unique_ptr<options::HolderPARALLEL> d_parallel;
    std::unique_ptr<options::HolderPARSER> d_parser;
    std::unique_ptr<options::HolderPRINTER> d_printer;
    std::unique_ptr<options::HolderPROOF> d_proof;
    std::unique_ptr<options::HolderPROP> d_prop;
    std::unique_ptr<options::HolderQUANTIFIERS> d_quantifiers;
    std::unique_ptr<options::HolderSEP> d_sep;
    std::unique_ptr<options::HolderSETS> d_sets;
    std::unique_ptr<options::HolderSMT> d_smt;
    std::unique_ptr<options::HolderSTRINGS> d_strings;
    std::unique_ptr<options::HolderTHEORY> d_theory;
    std::unique_ptr<options::HolderUF> d_uf;
// clang-format on
 public:
// clang-format off
  const options::HolderARITH& arith;
  options::HolderARITH& writeArith();
  const options::HolderARRAYS& arrays;
  options::HolderARRAYS& writeArrays();
  const options::HolderBASE& base;
  options::HolderBASE& writeBase();
  const options::HolderBOOLEANS& booleans;
  options::HolderBOOLEANS& writeBooleans();
  const options::HolderBUILTIN& builtin;
  options::HolderBUILTIN& writeBuiltin();
  const options::HolderBV& bv;
  options::HolderBV& writeBv();
  const options::HolderDATATYPES& datatypes;
  options::HolderDATATYPES& writeDatatypes();
  const options::HolderDECISION& decision;
  options::HolderDECISION& writeDecision();
  const options::HolderEXPR& expr;
  options::HolderEXPR& writeExpr();
  const options::HolderFF& ff;
  options::HolderFF& writeFf();
  const options::HolderFP& fp;
  options::HolderFP& writeFp();
  const options::HolderDRIVER& driver;
  options::HolderDRIVER& writeDriver();
  const options::HolderPARALLEL& parallel;
  options::HolderPARALLEL& writeParallel();
  const options::HolderPARSER& parser;
  options::HolderPARSER& writeParser();
  const options::HolderPRINTER& printer;
  options::HolderPRINTER& writePrinter();
  const options::HolderPROOF& proof;
  options::HolderPROOF& writeProof();
  const options::HolderPROP& prop;
  options::HolderPROP& writeProp();
  const options::HolderQUANTIFIERS& quantifiers;
  options::HolderQUANTIFIERS& writeQuantifiers();
  const options::HolderSEP& sep;
  options::HolderSEP& writeSep();
  const options::HolderSETS& sets;
  options::HolderSETS& writeSets();
  const options::HolderSMT& smt;
  options::HolderSMT& writeSmt();
  const options::HolderSTRINGS& strings;
  options::HolderSTRINGS& writeStrings();
  const options::HolderTHEORY& theory;
  options::HolderTHEORY& writeTheory();
  const options::HolderUF& uf;
  options::HolderUF& writeUf();
// clang-format on
  
 private:
  /** The handler for the options of the theory. */
  std::unique_ptr<options::OptionsHandler> d_handler;
}; /* class Options */

}  // namespace cvc5::internal

#endif /* CVC5__OPTIONS__OPTIONS_H */
