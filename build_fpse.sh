#!/bin/bash
set -x
set -e

# link gsl_runtime lib
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgslcblas.so /usr/lib/libgslcblas.so.0
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgsl.so /usr/lib/libgsl.so.25
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libkleeRuntest.so /usr/lib/libkleeRuntest.so.1.0

# link dreal lib
sudo ln -s /opt/dreal/4.21.06.2/lib/libdreal.so /usr/lib/libdreal.so
sudo ln -s /opt/libibex/2.7.4/lib/libibex.so /usr/lib/libibex.so

cd /home/aaa/fp-solver/klee-float-solver_1
mkdir -p build
cd build
cmake -DENABLE_SOLVER_Z3=ON  \
   -DENABLE_SOLVER_STP=OFF \
   -DENABLE_POSIX_RUNTIME=ON \
   -DENABLE_KLEE_UCLIBC=ON \
   -DENABLE_UNIT_TESTS=OFF \
   -DENABLE_SYSTEM_TESTS=OFF \
   -DCMAKE_BUILD_TYPE=Release  ..

make -j$(nproc)
make install
