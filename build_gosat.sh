#!/bin/bash

# This script builds Z3
set -x
set -e

cd /home/aaa/fp-solver/gosat
mkdir -p build
cd build
cmake -DCMAKE_BUILD_TYPE=Release ..

make -j$(nproc)
make install
