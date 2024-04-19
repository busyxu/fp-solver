/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Tim King, Aina Niemetz
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
 */

#include "options/options.h"

#include "base/check.h"
#include "base/cvc5config.h"
#include "options/options_handler.h"
#include "options/options_listener.h"

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
// clang-format on

namespace cvc5::internal
{
  Options::Options()
      :
// clang-format off
        d_arith(std::make_unique<options::HolderARITH>()),
        d_arrays(std::make_unique<options::HolderARRAYS>()),
        d_base(std::make_unique<options::HolderBASE>()),
        d_booleans(std::make_unique<options::HolderBOOLEANS>()),
        d_builtin(std::make_unique<options::HolderBUILTIN>()),
        d_bv(std::make_unique<options::HolderBV>()),
        d_datatypes(std::make_unique<options::HolderDATATYPES>()),
        d_decision(std::make_unique<options::HolderDECISION>()),
        d_expr(std::make_unique<options::HolderEXPR>()),
        d_ff(std::make_unique<options::HolderFF>()),
        d_fp(std::make_unique<options::HolderFP>()),
        d_driver(std::make_unique<options::HolderDRIVER>()),
        d_parallel(std::make_unique<options::HolderPARALLEL>()),
        d_parser(std::make_unique<options::HolderPARSER>()),
        d_printer(std::make_unique<options::HolderPRINTER>()),
        d_proof(std::make_unique<options::HolderPROOF>()),
        d_prop(std::make_unique<options::HolderPROP>()),
        d_quantifiers(std::make_unique<options::HolderQUANTIFIERS>()),
        d_sep(std::make_unique<options::HolderSEP>()),
        d_sets(std::make_unique<options::HolderSETS>()),
        d_smt(std::make_unique<options::HolderSMT>()),
        d_strings(std::make_unique<options::HolderSTRINGS>()),
        d_theory(std::make_unique<options::HolderTHEORY>()),
        d_uf(std::make_unique<options::HolderUF>()),
        arith(*d_arith),
        arrays(*d_arrays),
        base(*d_base),
        booleans(*d_booleans),
        builtin(*d_builtin),
        bv(*d_bv),
        datatypes(*d_datatypes),
        decision(*d_decision),
        expr(*d_expr),
        ff(*d_ff),
        fp(*d_fp),
        driver(*d_driver),
        parallel(*d_parallel),
        parser(*d_parser),
        printer(*d_printer),
        proof(*d_proof),
        prop(*d_prop),
        quantifiers(*d_quantifiers),
        sep(*d_sep),
        sets(*d_sets),
        smt(*d_smt),
        strings(*d_strings),
        theory(*d_theory),
        uf(*d_uf),
// clang-format on
        d_handler(std::make_unique<options::OptionsHandler>(this))
  {
  }

  Options::~Options() {}

// clang-format off
  options::HolderARITH& Options::writeArith()
  {
    return *d_arith;
  }

  options::HolderARRAYS& Options::writeArrays()
  {
    return *d_arrays;
  }

  options::HolderBASE& Options::writeBase()
  {
    return *d_base;
  }

  options::HolderBOOLEANS& Options::writeBooleans()
  {
    return *d_booleans;
  }

  options::HolderBUILTIN& Options::writeBuiltin()
  {
    return *d_builtin;
  }

  options::HolderBV& Options::writeBv()
  {
    return *d_bv;
  }

  options::HolderDATATYPES& Options::writeDatatypes()
  {
    return *d_datatypes;
  }

  options::HolderDECISION& Options::writeDecision()
  {
    return *d_decision;
  }

  options::HolderEXPR& Options::writeExpr()
  {
    return *d_expr;
  }

  options::HolderFF& Options::writeFf()
  {
    return *d_ff;
  }

  options::HolderFP& Options::writeFp()
  {
    return *d_fp;
  }

  options::HolderDRIVER& Options::writeDriver()
  {
    return *d_driver;
  }

  options::HolderPARALLEL& Options::writeParallel()
  {
    return *d_parallel;
  }

  options::HolderPARSER& Options::writeParser()
  {
    return *d_parser;
  }

  options::HolderPRINTER& Options::writePrinter()
  {
    return *d_printer;
  }

  options::HolderPROOF& Options::writeProof()
  {
    return *d_proof;
  }

  options::HolderPROP& Options::writeProp()
  {
    return *d_prop;
  }

  options::HolderQUANTIFIERS& Options::writeQuantifiers()
  {
    return *d_quantifiers;
  }

  options::HolderSEP& Options::writeSep()
  {
    return *d_sep;
  }

  options::HolderSETS& Options::writeSets()
  {
    return *d_sets;
  }

  options::HolderSMT& Options::writeSmt()
  {
    return *d_smt;
  }

  options::HolderSTRINGS& Options::writeStrings()
  {
    return *d_strings;
  }

  options::HolderTHEORY& Options::writeTheory()
  {
    return *d_theory;
  }

  options::HolderUF& Options::writeUf()
  {
    return *d_uf;
  }

// clang-format on

  void Options::copyValues(const Options& options)
  {
    if (this != &options)
    {
// clang-format off
      *d_arith = *options.d_arith;
      *d_arrays = *options.d_arrays;
      *d_base = *options.d_base;
      *d_booleans = *options.d_booleans;
      *d_builtin = *options.d_builtin;
      *d_bv = *options.d_bv;
      *d_datatypes = *options.d_datatypes;
      *d_decision = *options.d_decision;
      *d_expr = *options.d_expr;
      *d_ff = *options.d_ff;
      *d_fp = *options.d_fp;
      *d_driver = *options.d_driver;
      *d_parallel = *options.d_parallel;
      *d_parser = *options.d_parser;
      *d_printer = *options.d_printer;
      *d_proof = *options.d_proof;
      *d_prop = *options.d_prop;
      *d_quantifiers = *options.d_quantifiers;
      *d_sep = *options.d_sep;
      *d_sets = *options.d_sets;
      *d_smt = *options.d_smt;
      *d_strings = *options.d_strings;
      *d_theory = *options.d_theory;
      *d_uf = *options.d_uf;
// clang-format on
    }
  }

}  // namespace cvc5::internal

