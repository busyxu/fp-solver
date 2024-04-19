#!/bin/bash

# This script builds Z3
set -x
set -e

#cd /home/aaa/fp-solver
#rm -rf gmp-6.2.0x/
#tar -xvf gmp-6.2.0x.tar.xz
#cd gmp-6.2.0x 
#./configure --enable-cxx

cd /home/aaa/fp-solver
./configure --enable-cxx

make -j$(nproc)
sudo make install
