#!/bin/bash

# This script builds Z3
set -x
set -e

cd /home/aaa/fp-solver/klee-uclibc
./configure --make-llvm-lib
make -j$(nproc)
