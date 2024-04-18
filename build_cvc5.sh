#!/bin/bash
set -x
set -e
set -o pipefail


#sudo apt-get install libssl-dev python3-pip
#/usr/bin/python3 -m pip install tomli
#/usr/bin/python3 -m pip install pyparsing

#sudo apt-get install libssl-dev

cd /home/aaa/fp-solcer
sudo tar -xvzf cmake-3.22.1.tar.gz -C /usr/share

cd /usr/share/cmake-3.22.1
sudo chmod 777 ./configure
sudo ./configure
sudo make -j$(nproc)
sudo make install
sudo update-alternatives --install /usr/bin/cmake cmake /usr/local/bin/cmake 1 --force

cd /home/aaa/fp-solver/cvc5
./configure.sh --prefix=/home/aaa/fp-solver/cvc5/install --no-java-bindings --no-python-bindings --auto-download
cd build   # default is ./build
make -j$(nproc)
# Install to avoid the libtool crap!
make install
