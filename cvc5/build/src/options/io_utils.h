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
 * IO manipulation classes.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__IO_UTILS_H
#define CVC5__OPTIONS__IO_UTILS_H

#include <iosfwd>

#include "options/language.h"
#include "options/printer_options.h"

/**
 * A collection of utilities to apply options that change how we print objects
 * (mostly nodes) to streams. The core idea is to attach the options to every
 * stream via `std::ios_base::iword()`, allowing both persistent options that
 * are associated to a stream (and thus in place even when the code using it has
 * no access to options) and options that are different for different output
 * streams.
 *
 * The options should call the appropriate `setDefault*` when an option is set,
 * which changes the default for streams that have no values set yet.
 * For any object derived from `std::ios_base` (this includes all standard
 * streams), `apply*()` will set the given values on the given object while
 * `get*()` retrieves the specified option.
 */
namespace cvc5::internal::options::ioutils {

// clang-format off

void setDefaultBvPrintConstsAsIndexedSymbols(bool value);
void applyBvPrintConstsAsIndexedSymbols(std::ios_base& ios, bool value) CVC5_EXPORT;
bool getBvPrintConstsAsIndexedSymbols(std::ios_base& ios);

void setDefaultDagThresh(int64_t value);
void applyDagThresh(std::ios_base& ios, int64_t value) CVC5_EXPORT;
int64_t getDagThresh(std::ios_base& ios);

void setDefaultNodeDepth(int64_t value);
void applyNodeDepth(std::ios_base& ios, int64_t value) CVC5_EXPORT;
int64_t getNodeDepth(std::ios_base& ios);

void setDefaultFlattenHOChains(bool value);
void applyFlattenHOChains(std::ios_base& ios, bool value) CVC5_EXPORT;
bool getFlattenHOChains(std::ios_base& ios);

void setDefaultModelUninterpPrint(ModelUninterpPrintMode value);
void applyModelUninterpPrint(std::ios_base& ios, ModelUninterpPrintMode value) CVC5_EXPORT;
ModelUninterpPrintMode getModelUninterpPrint(std::ios_base& ios);

void setDefaultOutputLanguage(Language value);
void applyOutputLanguage(std::ios_base& ios, Language value) CVC5_EXPORT;
Language getOutputLanguage(std::ios_base& ios);
// clang-format on

/**
 * A scope to copy and restore the options on an `std::ios_base` object in an
 * RAII-style fashion.
 * The options are read from the ios object on construction and restored on
 * destruction of the scope.
 */
class CVC5_EXPORT Scope
{
 public:
  /** Copy the options from the ios object */
  Scope(std::ios_base& ios);
  /** Copy the options from the ios object */
  ~Scope();

 private:
  /** The ios object */
  std::ios_base& d_ios;

// clang-format off
  bool d_bvPrintConstsAsIndexedSymbols;
  int64_t d_dagThresh;
  int64_t d_nodeDepth;
  bool d_flattenHOChains;
  ModelUninterpPrintMode d_modelUninterpPrint;
  Language d_outputLanguage;
// clang-format on
};
}  // namespace cvc5::internal::options::ioutils

#endif /* CVC5__OPTIONS__IO_UTILS_H */
