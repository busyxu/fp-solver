#!/bin/bash

# This script builds Z3
set -x
set -e

cd /home/aaa/fp-solver/bitwuzla

./contrib/setup-cadical.sh
# Download and build BTOR2Tools
./contrib/setup-btor2tools.sh
# Download and build SymFPU
./contrib/setup-symfpu.sh

./configure.sh --shared --prefix /home/aaa/fp-solver/bitwuzla/install
cd build
make -j$(nproc)
make install
