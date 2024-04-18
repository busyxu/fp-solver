ARG BASE_IMAGE
FROM ${BASE_IMAGE}

RUN sudo apt-get update
RUN sudo apt-get -y --no-install-recommends install  \
    build-essential  \
    cmake  \
    curl  \
    file  \
    g++-multilib  \
    gcc-multilib  \
    git  \
    libcap-dev  \
    libgoogle-perftools-dev  \
    libncurses5-dev  \
    libsqlite3-dev  \
    libtcmalloc-minimal4  \
    python3-pip  \
    unzip  \
    graphviz  \
    doxygen  \
    pkg-config \
    m4

RUN pip3 install lit tabulate wllvm tomli pyparsing -i https://pypi.tuna.tsinghua.edu.cn/simple

# pull fp-solver
RUN git clone https://github.com/busyxu/fp-solver.git
RUN cd /home/aaa/fp-solver && git checkout docker_fpse

# Install LLVM-6
RUN /home/aaa/fp-solver/build_llvm-6.sh

# Build Z3 4.6.2
RUN /home/aaa/fp-solver/build_z3-4.6.2.sh

# setting env
ENV PATH="$PATH:/home/aaa/fp-solver/llvm-6/build:/home/aaa/fp-solver/llvm-6/install/bin:/home/aaa/fp-solver/z3-4.6.2/build:/home/aaa/fp-solver/z3-4.6.2/install/bin"

# Install klee-uclibc
RUN /home/aaa/fp-solver/build_klee-uclibc.sh

# Install zlib
RUN /home/aaa/fp-solver/build_zlib-1.2.11.sh

# Install gmp-6.2.0x
RUN rm -rf /home/aaa/fp-solver/gmp-6.2.0x
ADD gmp-6.2.0x.tar.xz /home/aaa/fp-solver
RUN /home/aaa/fp-solver/build_gmp-6.2.0x.sh

# install json-c
RUN /home/aaa/fp-solver/build_json-c.sh

# remake gsl


# link gsl_runtime_lib

# install bitwuzla
RUN /home/aaa/fp-solver/build_bitwuzla.sh

# install mathsat5 'tar'


# install cvc5
RUN /home/aaa/fp-solver/build_cvc5.sh

# install dreal
RUN /home/aaa/fp-solver/build_dreal.sh

# install nlopt
RUN /home/aaa/fp-solver/build_nlopt.sh

# install gosat
RUN /home/aaa/fp-solver/build_gosat.sh

# install klee-float-solver include jfs
RUN /home/aaa/fp-solver/build_fpse.sh

# copy analysis





