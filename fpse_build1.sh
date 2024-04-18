#!/bin/bash
set -x
set -e

# clone project
#git config --global http.proxy socks5://192.168.134.180:10808
#git config --global https.proxy socks5://192.168.134.180:10808
#git config --global user.email "you@example.com"
#git config --global user.name "yangxu"
git clone https://github.com/busyxu/fp-solver.git
cd /home/aaa/fp-solver
git checkout docker_fpse

# install llvm-6
cd /home/aaa/fp-solver/llvm-6
mkdir -p build
cd build
cmake \
     -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/llvm-6/install \
     -DCMAKE_BUILD_TYPE=Release \
     -DLLVM_TARGETS_TO_BUILD=X86 \
     -DLLVM_ENABLE_RTTI=OFF \
     -DLLVM_ENABLE_EH=OFF \
     -DLLVM_ENABLE_LTO=OFF \
     -DLLVM_BUILD_LLVM_DYLIB=OFF \
     -DBUILD_SHARED_LIBS=OFF \
     ..
make -j $(nproc)
make install

# install z3-4.6.2
cd /home/aaa/fp-solver/z3-4.6.2
mkdir -p build
cd build 
cmake \
    -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/z3-4.6.2/install \
    -DCMAKE_BUILD_TYPE=Release ..
make -j $(nproc)
make install

# setting env path
echo 'export PATH="$PATH:/home/aaa/fp-solver/llvm-6/build"' >> /root/.bashrc
echo 'export PATH="$PATH:/home/aaa/fp-solver/llvm-6/install/bin"' >> /root/.bashrc
echo 'export PATH="$PATH:/home/aaa/fp-solver/z3-4.6.2/build"' >> /root/.bashrc
echo 'export PATH="$PATH:/home/aaa/fp-solver/z3-4.6.2/install/bin"' >> /root/.bashrc

# make klee-uclib
cd /home/aaa/fp-solver/klee-uclibc
./configure --make-llvm-lib
make

# install zlib
cd /home/aaa/fp-solver/zlib-1.2.11
./configure
make
sudo make install

# install gmp-6.2.0x
cd /home/aaa/fp-solver/gmp-6.2.0x
./configure --enable-cxx
make -j $(nproc)
sudo make install

# install Json-C
cd /home/aaa/fp-solver/json-c
mkdir -p build
cd build
cmake -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/json-c/install ..
make
make install

# link gsl_runtime lib
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgslcblas.so /usr/lib/libgslcblas.so.0
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgsl.so /usr/lib/libgsl.so.25
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libkleeRuntest.so /usr/lib/libkleeRuntest.so.1.0

# install dreal
cd /home/aaa/fp-solver/dreal_install
sudo ./install_dreal.sh
sudo ln -s /opt/dreal/4.21.06.2/lib/libdreal.so /usr/lib/libdreal.so
sudo ln -s /opt/libibex/2.7.4/lib/libibex.so /usr/lib/libibex.so

# install nlopt
#cd nlopt
#mkdir -p build
#cd build
#cmake -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/nlopt/install ..
#make -j $(nproc)
#make install

# install gosat
#cd gosat
#mkdir -p build
#cd build
#cmake -DCMAKE_BUILD_TYPE=Release ..
#make -j $(nproc)

# install bitwuzla
#./configure.sh --shared --prefix /home/aaa/fp-solver/bitwuzla/install
#cd build
#make make -j $(nproc)
#make install

# install cvc5

#install mathsat5

# klee-float-solver
#cd klee-float-solver_1
#mkdir -p build
#cd build
#cmake -DENABLE_SOLVER_Z3=ON  \
#   -DENABLE_SOLVER_STP=OFF \
#   -DENABLE_POSIX_RUNTIME=ON \
#   -DENABLE_KLEE_UCLIBC=ON \
#   -DENABLE_UNIT_TESTS=OFF \
#   -DENABLE_SYSTEM_TESTS=OFF \
#   -DCMAKE_BUILD_TYPE=Release  ..
#make -j $(nproc)


