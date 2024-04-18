#!/bin/bash

# This script builds Z3
set -x
set -e

cd /home/aaa/fp-solver/nlopt
mkdir -p build
cd build
cmake -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/nlopt/install ..

make -j$(nproc)
make install
