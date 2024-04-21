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
