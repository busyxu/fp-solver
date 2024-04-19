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

#include <iomanip>
#include <iostream>

#include "options/io_utils.h"

namespace cvc5::internal::options::ioutils {
namespace {

// There is no good way to figure out whether the value behind iword() was
// explicitly set. The default value is zero; we shift by some random constant
// such that zero is never a valid value, and we can still use both negative
// and positive values.
static constexpr long value_offset = 1024;

template <typename T>
void setData(std::ios_base& ios, int iosIndex, T value)
{
  ios.iword(iosIndex) = static_cast<long>(value) + value_offset;
}
template <typename T>
T getData(std::ios_base& ios, int iosIndex, T defaultValue)
{
  long& l = ios.iword(iosIndex);
  if (l == 0)
  {
    return defaultValue;
  }
  return static_cast<T>(l - value_offset);
}

}  // namespace

// clang-format off

const static int s_iosBvPrintConstsAsIndexedSymbols = std::ios_base::xalloc();
static thread_local bool s_bvPrintConstsAsIndexedSymbolsDefault = false;
void setDefaultBvPrintConstsAsIndexedSymbols(bool value) { s_bvPrintConstsAsIndexedSymbolsDefault = value; }
void applyBvPrintConstsAsIndexedSymbols(std::ios_base& ios, bool value) { setData(ios, s_iosBvPrintConstsAsIndexedSymbols, value); }
bool getBvPrintConstsAsIndexedSymbols(std::ios_base& ios) { return getData(ios, s_iosBvPrintConstsAsIndexedSymbols, s_bvPrintConstsAsIndexedSymbolsDefault); }


const static int s_iosDagThresh = std::ios_base::xalloc();
static thread_local int64_t s_dagThreshDefault = 1;
void setDefaultDagThresh(int64_t value) { s_dagThreshDefault = value; }
void applyDagThresh(std::ios_base& ios, int64_t value) { setData(ios, s_iosDagThresh, value); }
int64_t getDagThresh(std::ios_base& ios) { return getData(ios, s_iosDagThresh, s_dagThreshDefault); }


const static int s_iosNodeDepth = std::ios_base::xalloc();
static thread_local int64_t s_nodeDepthDefault = -1;
void setDefaultNodeDepth(int64_t value) { s_nodeDepthDefault = value; }
void applyNodeDepth(std::ios_base& ios, int64_t value) { setData(ios, s_iosNodeDepth, value); }
int64_t getNodeDepth(std::ios_base& ios) { return getData(ios, s_iosNodeDepth, s_nodeDepthDefault); }


const static int s_iosFlattenHOChains = std::ios_base::xalloc();
static thread_local bool s_flattenHOChainsDefault = false;
void setDefaultFlattenHOChains(bool value) { s_flattenHOChainsDefault = value; }
void applyFlattenHOChains(std::ios_base& ios, bool value) { setData(ios, s_iosFlattenHOChains, value); }
bool getFlattenHOChains(std::ios_base& ios) { return getData(ios, s_iosFlattenHOChains, s_flattenHOChainsDefault); }


const static int s_iosModelUninterpPrint = std::ios_base::xalloc();
static thread_local ModelUninterpPrintMode s_modelUninterpPrintDefault = ModelUninterpPrintMode::None;
void setDefaultModelUninterpPrint(ModelUninterpPrintMode value) { s_modelUninterpPrintDefault = value; }
void applyModelUninterpPrint(std::ios_base& ios, ModelUninterpPrintMode value) { setData(ios, s_iosModelUninterpPrint, value); }
ModelUninterpPrintMode getModelUninterpPrint(std::ios_base& ios) { return getData(ios, s_iosModelUninterpPrint, s_modelUninterpPrintDefault); }


const static int s_iosOutputLanguage = std::ios_base::xalloc();
static thread_local Language s_outputLanguageDefault = Language::LANG_AUTO;
void setDefaultOutputLanguage(Language value) { s_outputLanguageDefault = value; }
void applyOutputLanguage(std::ios_base& ios, Language value) { setData(ios, s_iosOutputLanguage, value); }
Language getOutputLanguage(std::ios_base& ios) { return getData(ios, s_iosOutputLanguage, s_outputLanguageDefault); }

// clang-format on

Scope::Scope(std::ios_base& ios)
    : d_ios(ios),
// clang-format off
      d_bvPrintConstsAsIndexedSymbols(getBvPrintConstsAsIndexedSymbols(d_ios)),
      d_dagThresh(getDagThresh(d_ios)),
      d_nodeDepth(getNodeDepth(d_ios)),
      d_flattenHOChains(getFlattenHOChains(d_ios)),
      d_modelUninterpPrint(getModelUninterpPrint(d_ios)),
      d_outputLanguage(getOutputLanguage(d_ios))
// clang-format on
{
}

Scope::~Scope()
{
// clang-format off
  applyBvPrintConstsAsIndexedSymbols(d_ios, d_bvPrintConstsAsIndexedSymbols);
  applyDagThresh(d_ios, d_dagThresh);
  applyNodeDepth(d_ios, d_nodeDepth);
  applyFlattenHOChains(d_ios, d_flattenHOChains);
  applyModelUninterpPrint(d_ios, d_modelUninterpPrint);
  applyOutputLanguage(d_ios, d_outputLanguage);
// clang-format on
}

}  // namespace cvc5::internal::options::ioutils
