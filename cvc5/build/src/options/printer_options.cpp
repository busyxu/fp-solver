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
 * Option template for option modules.
 *
 * For each <module>_options.toml configuration file, mkoptions.py
 * expands this template and generates a <module>_options.cpp file.
 */
#include "options/printer_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, ModelUninterpPrintMode mode)
{
  switch(mode)
  {
    case ModelUninterpPrintMode::DeclSortAndFun: return os << "decl-sort-and-fun";
    case ModelUninterpPrintMode::DeclFun: return os << "decl-fun";
    case ModelUninterpPrintMode::None: return os << "none";
    default: Unreachable();
  }
  return os;
}
ModelUninterpPrintMode stringToModelUninterpPrintMode(const std::string& optarg)
{
  if (optarg == "decl-sort-and-fun") return ModelUninterpPrintMode::DeclSortAndFun;
  else if (optarg == "decl-fun") return ModelUninterpPrintMode::DeclFun;
  else if (optarg == "none") return ModelUninterpPrintMode::None;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  uninterpreted elements in models printing modes.
Available modes for --model-u-print are:
+ decl-sort-and-fun
  print uninterpreted elements declare-fun, and also include a declare-sort for
  the sort
+ decl-fun
  print uninterpreted elements declare-fun, but don't include a declare-sort for
  the sort
+ none (default)
  (default) do not print declarations of uninterpreted elements in models.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --model-u-print: `") +
                        optarg + "'.  Try --model-u-print=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
