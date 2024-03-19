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
#include "options/uf_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, UfssMode mode)
{
  switch(mode)
  {
    case UfssMode::FULL: return os << "full";
    case UfssMode::NO_MINIMAL: return os << "no-minimal";
    case UfssMode::NONE: return os << "none";
    default: Unreachable();
  }
  return os;
}
UfssMode stringToUfssMode(const std::string& optarg)
{
  if (optarg == "full") return UfssMode::FULL;
  else if (optarg == "no-minimal") return UfssMode::NO_MINIMAL;
  else if (optarg == "none") return UfssMode::NONE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  UF with cardinality options currently supported by the --uf-ss option when
  combined with finite model finding.
Available modes for --uf-ss are:
+ full (default)
  Default, use UF with cardinality to find minimal models for uninterpreted
  sorts.
+ no-minimal
  Use UF with cardinality to shrink models, but do no enforce minimality.
+ none
  Do not use UF with cardinality to shrink model sizes.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --uf-ss: `") +
                        optarg + "'.  Try --uf-ss=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
