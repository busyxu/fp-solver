#!/bin/bash

# This script builds Z3
set -x
set -e

cd /home/aaa/fp-solver/dreal_install
./install_dreal.sh

make -j$(nproc)
