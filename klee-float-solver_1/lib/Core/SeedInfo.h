//===-- SeedInfo.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SEEDINFO_H
#define KLEE_SEEDINFO_H

#include "klee/Expr/Assignment.h"

extern "C" {
  struct KTest;
  struct KTestObject;
}

namespace klee {
  class ExecutionState;
  class TimingSolver;
  class MemoryObject;

  class SeedInfo {
  public:
    Assignment assignment;
    KTest *input;
    unsigned inputPosition;
    std::set<struct KTestObject*> used;
    
  public:
    explicit
    SeedInfo(KTest *_input) : assignment(true),
                             input(_input),
                             inputPosition(0) {}
    
    KTestObject *getNextInput(const MemoryObject *mo,
                             bool byName);
    
    /// Patch the seed so that condition is satisfied while retaining as
    /// many of the seed values as possible.
    void patchSeed(ExecutionState &state,
                   ref<Expr> condition,
                   TimingSolver *solver);

    //add by zgf : to support concreteSeed
    SeedInfo(Assignment assign) : assignment(assign),
                              input(NULL),
                              inputPosition(0) {}
  };
}

#endif /* KLEE_SEEDINFO_H */
