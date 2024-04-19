#!/bin/bash
set -x
set -e
set -o pipefail


cd /home/aaa/fp-solver
sudo tar -xvzf cmake-3.22.1.tar.gz -C /usr/share

cd /usr/share/cmake-3.22.1
sudo chmod 777 ./configure
sudo ./configure
sudo make -j$(nproc)
sudo make install
sudo update-alternatives --install /usr/bin/cmake cmake /usr/local/bin/cmake 1 --force

cd /home/aaa/fp-solver/cvc5
./configure.sh --prefix=/home/aaa/fp-solver/cvc5/install --no-java-bindings --no-python-bindings --auto-download
cp cvc5_deps/rewrites.cpp cvc5/build/src/rewriter/rewrites.cpp
cp cvc5_deps/rewrites.h cvc5/build/src/rewriter/rewrites.h
cd build   # default is ./build
sudo make -j$(nproc)
# Install to avoid the libtool crap!
sudo make install
