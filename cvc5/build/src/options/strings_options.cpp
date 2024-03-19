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
#include "options/strings_options.h"

#include <iostream>

#include "base/check.h"
#include "options/option_exception.h"

namespace cvc5::internal::options {

// clang-format off
std::ostream& operator<<(std::ostream& os, RegExpElimMode mode)
{
  switch(mode)
  {
    case RegExpElimMode::OFF: return os << "off";
    case RegExpElimMode::ON: return os << "on";
    case RegExpElimMode::AGG: return os << "agg";
    default: Unreachable();
  }
  return os;
}
RegExpElimMode stringToRegExpElimMode(const std::string& optarg)
{
  if (optarg == "off") return RegExpElimMode::OFF;
  else if (optarg == "on") return RegExpElimMode::ON;
  else if (optarg == "agg") return RegExpElimMode::AGG;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Regular expression elimination modes.
Available modes for --re-elim are:
+ off (default)
  Do not use regular expression elimination.
+ on
  Use regular expression elimination.
+ agg
  Use aggressive regular expression elimination.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --re-elim: `") +
                        optarg + "'.  Try --re-elim=help.");
}
std::ostream& operator<<(std::ostream& os, RegExpInterMode mode)
{
  switch(mode)
  {
    case RegExpInterMode::ALL: return os << "all";
    case RegExpInterMode::CONSTANT: return os << "constant";
    case RegExpInterMode::ONE_CONSTANT: return os << "one-constant";
    case RegExpInterMode::NONE: return os << "none";
    default: Unreachable();
  }
  return os;
}
RegExpInterMode stringToRegExpInterMode(const std::string& optarg)
{
  if (optarg == "all") return RegExpInterMode::ALL;
  else if (optarg == "constant") return RegExpInterMode::CONSTANT;
  else if (optarg == "one-constant") return RegExpInterMode::ONE_CONSTANT;
  else if (optarg == "none") return RegExpInterMode::NONE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Regular expression intersection modes.
Available modes for --re-inter-mode are:
+ all
  Compute intersections for all regular expressions.
+ constant
  Compute intersections only between regular expressions that do not contain
  re.allchar or re.range.
+ one-constant
  Compute intersections only between regular expressions such that at least one
  side does not contain re.allchar or re.range.
+ none (default)
  Do not compute intersections for regular expressions.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --re-inter-mode: `") +
                        optarg + "'.  Try --re-inter-mode=help.");
}
std::ostream& operator<<(std::ostream& os, SeqArrayMode mode)
{
  switch(mode)
  {
    case SeqArrayMode::LAZY: return os << "lazy";
    case SeqArrayMode::EAGER: return os << "eager";
    case SeqArrayMode::NONE: return os << "none";
    default: Unreachable();
  }
  return os;
}
SeqArrayMode stringToSeqArrayMode(const std::string& optarg)
{
  if (optarg == "lazy") return SeqArrayMode::LAZY;
  else if (optarg == "eager") return SeqArrayMode::EAGER;
  else if (optarg == "none") return SeqArrayMode::NONE;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  use array-inspired solver for sequence updates in eager or lazy mode
Available modes for --seq-array are:
+ lazy
  use array-inspired solver for sequence updates in lazy mode
+ eager
  use array-inspired solver for sequence updates in eager mode
+ none (default)
  do not use array-inspired solver for sequence updates
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --seq-array: `") +
                        optarg + "'.  Try --seq-array=help.");
}
std::ostream& operator<<(std::ostream& os, ProcessLoopMode mode)
{
  switch(mode)
  {
    case ProcessLoopMode::FULL: return os << "full";
    case ProcessLoopMode::SIMPLE: return os << "simple";
    case ProcessLoopMode::SIMPLE_ABORT: return os << "simple-abort";
    case ProcessLoopMode::NONE: return os << "none";
    case ProcessLoopMode::ABORT: return os << "abort";
    default: Unreachable();
  }
  return os;
}
ProcessLoopMode stringToProcessLoopMode(const std::string& optarg)
{
  if (optarg == "full") return ProcessLoopMode::FULL;
  else if (optarg == "simple") return ProcessLoopMode::SIMPLE;
  else if (optarg == "simple-abort") return ProcessLoopMode::SIMPLE_ABORT;
  else if (optarg == "none") return ProcessLoopMode::NONE;
  else if (optarg == "abort") return ProcessLoopMode::ABORT;
  else if (optarg == "help")
  {
    std::cerr << R"FOOBAR(
  Loop processing modes.
Available modes for --strings-process-loop-mode are:
+ full (default)
  Perform full processing of looping word equations.
+ simple
  Omit normal loop breaking (default with --strings-fmf).
+ simple-abort
  Abort when normal loop breaking is required.
+ none
  Omit loop processing.
+ abort
  Abort if looping word equations are encountered.
)FOOBAR";
    std::exit(1);
  }
  throw OptionException(std::string("unknown option for --strings-process-loop-mode: `") +
                        optarg + "'.  Try --strings-process-loop-mode=help.");
}
// clang-format on

}  // namespace cvc5::internal::options
