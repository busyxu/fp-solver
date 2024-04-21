#!/bin/bash
set -x
set -e
set -o pipefail


pip3 install pyparsing

cd /home/aaa/fp-solver/cvc5
#./configure.sh --prefix=/home/aaa/fp-solver/cvc5/install --no-java-bindings --no-python-bindings --#auto-download
#cp cvc5_deps/rewrites.cpp cvc5/build/src/rewriter/rewrites.cpp
#cp cvc5_deps/rewrites.h cvc5/build/src/rewriter/rewrites.h
cd build   # default is ./build
make -j$(nproc)
# Install to avoid the libtool crap!
make install
