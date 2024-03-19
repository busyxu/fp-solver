环境：ubuntu18.04  python3.6    
llvm 6.0 + z3 4.6.2 + json-c + jfs + klee 2.3-pre +gsl

0. apt-get 环境预先安装
  可能需要换源
  sudo apt-get update
  sudo apt-get install build-essential cmake curl file g++-multilib gcc-multilib git libcap-dev libgoogle-perftools-dev libncurses5-dev libsqlite3-dev libtcmalloc-minimal4 python3-pip unzip graphviz doxygen pkg-config

  pip3 install lit tabulate wllvm -i https://pypi.tuna.tsinghua.edu.cn/simple


tar -xvf 文件名.tar.xz
tar -xvf 文件名.tar.xz -C /目标目录

1. 安装llvm 6.0，解压llvm四个包
  1.1. 将clang-tools-extra-6.0.0改名为extra，cfe-6.0.0改名为clang；
  1.2. 将compile-rt-6.0.0改名为compile-rt，llvm-6.0.0改名为llvm-6
  1.3. 将extra放入clang/tools中，clang放入llvm-6/tools中
  1.4. 将compile-rt 放入llvm-6/projects中
  1.5. mkdir build
  1.6. cd build
  1.7. cmake \
         -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/llvm-6/install \
         -DCMAKE_BUILD_TYPE=Release \
         -DLLVM_TARGETS_TO_BUILD=X86 \
         -DLLVM_ENABLE_RTTI=OFF \
         -DLLVM_ENABLE_EH=OFF \
         -DLLVM_ENABLE_LTO=OFF \
         -DLLVM_BUILD_LLVM_DYLIB=OFF \
         -DBUILD_SHARED_LIBS=OFF \
         ..
  1.8. make -j6
  #1.9. sudo make install
   make install


2. 编译安装Z3-4.6.2
  2.1. mkdir build
  2.2. cd build 
  2.3. cmake \
        -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/z3-4.6.2/install \
        -DCMAKE_BUILD_TYPE=Release   ..
  2.4. make -j6
  #2.5. sudo make install
  make install


3. 环境变量配置：
  3.1. sudo gedit ~/.bashrc
    export LLVM6_DIR=/home/aaa/fp-solver/llvm-6/build
    export LLVM6_BIN=/home/aaa/fp-solver/llvm-6/install/bin
    export Z3_DIR=/home/aaa/fp-solver/z3-4.6.2/build
    export Z3_BIN=/home/aaa/fp-solver/z3-4.6.2/install/bin
    export PATH=$PATH:$LLVM6_DIR:$LLVM6_BIN:$Z3_DIR:$Z3_BIN

  3.2. source ~/.bashrc


4. 编译klee-uclib
   4.1. git clone https://github.com/klee/klee-uclibc.git  
   4.2. cd klee-uclibc  
   4.3. ./configure --make-llvm-lib   
   4.4. make


5. 安装zlib库
   5.1. tar -xvzf zlib-1.2.11.tar.gz
   5.2. cd zlib-1.2.11
   5.3. ./configure
   5.4. make
   5.5. sudo make install
   #make install


6. 安装Json-C
   6.1. mkdir build
   6.2. cd build
   6.3. cmake -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/json-c/install ..
   6.4. make
   #6.5. sudo make install
   make install

7. 安装nlopt:
     >>mkdir build
     >>cd build
     >>cmake -DCMAKE_INSTALL_PREFIX=/home/aaa/fp-solver/nlopt/install ..
     >>make
     #>>sudo make install 
     make install

    sudo ln -s /home/aaa/fp-solver/nlopt/install/lib/libnlopt.so /usr/lib/libnlopt.so.0

8. 安装dreal，使用install脚本预先安装依赖，而后dpkg安装
  8.1. 运行./install_dreal.sh  注意，dreal的amd64包在同一路径下

  8.2. 将dreal库软链接到/usr/lib目录下
    sudo ln -s /opt/dreal/4.21.06.2/lib/libdreal.so /usr/lib/libdreal.so
    sudo ln -s /opt/libibex/2.7.4/lib/libibex.so /usr/lib/libibex.so


9. 是否要重新编译gsl_runtime库?  
  解压gsl_runtime;
  sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgslcblas.so /usr/lib/libgslcblas.so.0
  sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libgsl.so /usr/lib/libgsl.so.25
  sudo ln -s /home/aaa/fp-solver/gsl_runtime_lib/libkleeRuntest.so /usr/lib/libkleeRuntest.so.1.0


10. 编译gsl-gcov用于测量库函数中的覆盖率信息
   10.0. 注意要使用clang作为编译器，因为最终测试使用的是llvm-cov里的gcov组件进行覆盖率测试，
       为了保证gcov的版本一致性，所以需要指定clang。
       -fprofile-arcs -ftest-coverage这两个参数用于gcov覆盖率插桩（是否需要-lgcov？）
   10.1. cd gsl
   10.2. CC=clang   CFLAGS="-fprofile-arcs -ftest-coverage"  LIBS="-lm -lgcov"   ./configure    
   10.3. CC=clang make -j16   #编译生成lib，生成在.lib目录下
   10.4. 由于replay的最终目的是测量库函数的覆盖率信息，因此需要在gsl/specfunc/.libs中查看测试的驱动函数
       属于哪个.c文件，然后获得对应.c文件的gcov文件，再计算驱动函数内部的代码覆盖率


11. 安装GMP库，已有压缩包
  11.0. 前置安装m4
      sudo apt install m4
  #11.1. tar -xvJf gmp-6.2.0x.tar.lz  
  11.2. cd gmp-6.2.0x
  11.3. configure 开启c++库支持
      ./configure --enable-cxx 
  11.4. make
  11.5. sudo make install


12. 安装gosat
  12.0. 前置安装llvm-6,nlopt,
  12.1. 安装gosat， 修改cmakelist和llvm接口的版本
     >>mkdir build
     >>cd build
     >>cmake -DCMAKE_BUILD_TYPE=Release ..
     >>make
     ##>>sudo make install


13. 安装bitwuzla
  13.1 # Download and build Bitwuzla
    >>git clone https://github.com/bitwuzla/bitwuzla
    >>cd bitwuzla
  13.2 # Download and build CaDiCaL
    >>./contrib/setup-cadical.sh
  13.3 # Download and build BTOR2Tools
    >>./contrib/setup-btor2tools.sh
  13.4 # Download and build SymFPU
    >>./contrib/setup-symfpu.sh

  13.5 # Build Bitwuzla
    >>./configure.sh --shared --prefix /home/aaa/fp-solver/bitwuzla/install
    >>cd build
    >>make
    #>>sudo make install
    make install

   ### .a  .so 在build/lib下


14. 安装CVC5
  14.1 # 依赖
  >>/usr/bin/python3 -m pip install -i https://pypi.tuna.tsinghua.edu.cn/simple toml pyparsing
  >>sudo apt-get install flex bison libssl-dev
  14.2 # 升级cmake
  >>sudo tar -xvzf cmake-3.22.1.tar.gz -C /usr/share
  >>cd /usr/share/cmake-3.22.1
  >>sudo chmod 777 ./configure
  >>sudo ./configure
  >>sudo make -j8
  >>sudo make install
  >>sudo update-alternatives --install /usr/bin/cmake cmake /usr/local/bin/cmake 1 --force

  14.3 安装java
   >> sudo apt-get install default-jre
   >> sudo apt-get install default-jdk
  
  14.3 构建cvc5
    将本地/home/aaa/cvc5/build/deps/src下面的所有压缩包和.jar的资源文件全部考到服务器上的相应位置
    用本地/home/aaa/cvc5/buid/src/rewriter下的rewriter.h和rewriter.cpp替换掉服务器上的相应文件。
    >>./configure.sh --prefix=/home/aaa/fp-solver/cvc5/install --no-java-bindings --no-python-bindings --auto-download
    >> cd build
    >> make -j8
    #>> sudo make install
    make install

15. 安装MathSAT5 闭源项目
  >>xz -d mathsat-5.6.11.tar.xz
  >>tar -xvf mathsat-5.6.11.tar
  .a .so的依赖包在mathsat-5.6.11/lib下
  头文件在mathsat-5.6.11、include下


16. klee2.3-pre-float 安装，可以修改cmakelist指定llvm、z3等库的路径
   16.1. cd klee ; mkdir build; cd build
   16.2. cmake -DENABLE_SOLVER_Z3=ON  \
       -DENABLE_SOLVER_STP=OFF \
       -DENABLE_POSIX_RUNTIME=ON \
       -DENABLE_KLEE_UCLIBC=ON \
       -DENABLE_UNIT_TESTS=OFF \
       -DENABLE_SYSTEM_TESTS=OFF \
       -DCMAKE_BUILD_TYPE=Release  ..
   16.3. make -j16





统计所有driver的数量，总计301个driver
find . -name "*.c" | wc -l

统计当前已经获得的输出数量
find . -name *_output | wc -l

--fp2int-lib=/home/aaa/gsl_runtime_lib/softfloat.bc
complex_function.bc


服务器后台运行，输出打印信息
run:
>>nohup python3 multi_process.py & echo $! > test_pid.txt
stop:
>>kill -9 `cat test_pid.txt`

>>./replay.sh > replay_info.txt 2>&1


-watchdog 会抑制backpoint
