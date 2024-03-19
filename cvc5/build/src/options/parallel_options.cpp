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
#include "options/parallel_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, CheckMode mode)
{
  switch(mode)
  {
    case CheckMode::STANDARD: return os << "standard";
    case CheckMode::FULL: return os << "full";
    default: Unreachable();
  }
  return os;
}
CheckMode stringToCheckMode(const std::string& optarg)
{
  if (optarg == "standard") return CheckMode::STANDARD;
  else if (optarg == "full") return CheckMode::FULL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Partition check modes.
Available modes for --partition-check are:
+ standard (default)
  create partitions at standard checks
+ full
  create partitions at full checks
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --partition-check: `") +
                        optarg + "'.  Try --partition-check=help.");
}
std::ostream& operator<<(std::ostream& os, PartitionMode mode)
{
  switch(mode)
  {
    case PartitionMode::REVISED: return os << "revised";
    case PartitionMode::STRICT_CUBE: return os << "strict-cube";
    case PartitionMode::DECISION_TRAIL: return os << "decision-trail";
    case PartitionMode::HEAP_TRAIL: return os << "heap-trail";
    default: Unreachable();
  }
  return os;
}
PartitionMode stringToPartitionMode(const std::string& optarg)
{
  if (optarg == "revised") return PartitionMode::REVISED;
  else if (optarg == "strict-cube") return PartitionMode::STRICT_CUBE;
  else if (optarg == "decision-trail") return PartitionMode::DECISION_TRAIL;
  else if (optarg == "heap-trail") return PartitionMode::HEAP_TRAIL;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Partition strategy modes.
Available modes for --partition-strategy are:
+ revised (default)
  For 4 partitions, creates cubes C1, C2, C3, !C1 & !C2 & !C3
+ strict-cube
  For 4 partitions, creates cubes C1, !C1 & C2, !C1 & !C2 & C3, !C1 & !C2 & !C3
+ decision-trail
  Creates mutually exclusive cubes from the decisions in the SAT solver.
+ heap-trail
  Creates mutually exclusive cubes from the order heap in the SAT solver.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --partition-strategy: `") +
                        optarg + "'.  Try --partition-strategy=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
