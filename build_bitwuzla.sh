#!/bin/bash

# This script builds Z3
set -x
set -e

cd /home/aaa/fp-solver/bitwuzla

./configure.sh --shared --prefix /home/aaa/fp-solver/bitwuzla/install
cd build
make -j$(nproc)
make install
