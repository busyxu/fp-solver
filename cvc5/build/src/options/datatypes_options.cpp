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
#include "options/datatypes_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, SygusFairMode mode)
{
  switch(mode)
  {
    case SygusFairMode::DIRECT: return os << "direct";
    case SygusFairMode::DT_SIZE: return os << "dt-size";
    case SygusFairMode::DT_HEIGHT_PRED: return os << "dt-height-bound";
    case SygusFairMode::DT_SIZE_PRED: return os << "dt-size-bound";
    case SygusFairMode::NONE: return os << "none";
    default: Unreachable();
  }
  return os;
}
SygusFairMode stringToSygusFairMode(const std::string& optarg)
{
  if (optarg == "direct") return SygusFairMode::DIRECT;
  else if (optarg == "dt-size") return SygusFairMode::DT_SIZE;
  else if (optarg == "dt-height-bound") return SygusFairMode::DT_HEIGHT_PRED;
  else if (optarg == "dt-size-bound") return SygusFairMode::DT_SIZE_PRED;
  else if (optarg == "none") return SygusFairMode::NONE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for enforcing fairness for counterexample guided quantifier instantion.
Available modes for --sygus-fair are:
+ direct
  Enforce fairness using direct conflict lemmas.
+ dt-size (default)
  Enforce fairness using size operator.
+ dt-height-bound
  Enforce fairness by height bound predicate.
+ dt-size-bound
  Enforce fairness by size bound predicate.
+ none
  Do not enforce fairness.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-fair: `") +
                        optarg + "'.  Try --sygus-fair=help.");
}
std::ostream& operator<<(std::ostream& os, SygusRewriterMode mode)
{
  switch(mode)
  {
    case SygusRewriterMode::NONE: return os << "none";
    case SygusRewriterMode::BASIC: return os << "basic";
    case SygusRewriterMode::EXTENDED: return os << "extended";
    default: Unreachable();
  }
  return os;
}
SygusRewriterMode stringToSygusRewriterMode(const std::string& optarg)
{
  if (optarg == "none") return SygusRewriterMode::NONE;
  else if (optarg == "basic") return SygusRewriterMode::BASIC;
  else if (optarg == "extended") return SygusRewriterMode::EXTENDED;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for applying rewriting for sygus symmetry breaking.
Available modes for --sygus-rewriter are:
+ none
  Do not use the rewriter.
+ basic
  Use the basic rewriter.
+ extended (default)
  Use the extended rewriter.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-rewriter: `") +
                        optarg + "'.  Try --sygus-rewriter=help.");
}
std::ostream& operator<<(std::ostream& os, SygusSimpleSymBreakMode mode)
{
  switch(mode)
  {
    case SygusSimpleSymBreakMode::NONE: return os << "none";
    case SygusSimpleSymBreakMode::BASIC: return os << "basic";
    case SygusSimpleSymBreakMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
SygusSimpleSymBreakMode stringToSygusSimpleSymBreakMode(const std::string& optarg)
{
  if (optarg == "none") return SygusSimpleSymBreakMode::NONE;
  else if (optarg == "basic") return SygusSimpleSymBreakMode::BASIC;
  else if (optarg == "agg") return SygusSimpleSymBreakMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Modes for applying simple symmetry breaking based on the grammar for smart
  enumeration.
Available modes for --sygus-simple-sym-break are:
+ none
  Do not apply simple symmetry breaking.
+ basic
  Apply basic simple symmetry breaking.
+ agg (default)
  Apply aggressive simple symmetry breaking.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --sygus-simple-sym-break: `") +
                        optarg + "'.  Try --sygus-simple-sym-break=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
