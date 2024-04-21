#!/bin/bash
set -x
set -e

# link gsl_runtime lib
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgslcblas.so /usr/lib/libgslcblas.so.0
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgsl.so /usr/lib/libgsl.so.25
sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libkleeRuntest.so /usr/lib/libkleeRuntest.so.1.0

