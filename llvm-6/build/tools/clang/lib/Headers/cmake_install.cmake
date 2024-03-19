# Install script for directory: /home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/home/aaa/fp-solver/llvm-6/install")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Release")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xclang-headersx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/clang/6.0.0/include" TYPE FILE PERMISSIONS OWNER_READ OWNER_WRITE GROUP_READ WORLD_READ FILES
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/adxintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/altivec.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/ammintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/arm_acle.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/armintr.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/arm64intr.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx2intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512bwintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512bitalgintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vlbitalgintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512cdintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vpopcntdqintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512dqintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512erintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512fintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512ifmaintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512ifmavlintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512pfintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vbmiintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vbmivlintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vbmi2intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vlvbmi2intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vlbwintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vlcdintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vldqintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vlintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vpopcntdqvlintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vnniintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avx512vlvnniintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/avxintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/bmi2intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/bmiintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__clang_cuda_builtin_vars.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__clang_cuda_cmath.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__clang_cuda_complex_builtins.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__clang_cuda_intrinsics.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__clang_cuda_math_forward_declares.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__clang_cuda_runtime_wrapper.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/cetintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/clzerointrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/cpuid.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/clflushoptintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/clwbintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/emmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/f16cintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/float.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/fma4intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/fmaintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/fxsrintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/gfniintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/htmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/htmxlintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/ia32intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/immintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/inttypes.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/iso646.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/limits.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/lwpintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/lzcntintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/mm3dnow.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/mmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/mm_malloc.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/module.modulemap"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/msa.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/mwaitxintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/nmmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/opencl-c.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/pkuintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/pmmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/popcntintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/prfchwintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/rdseedintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/rtmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/s390intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/shaintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/smmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/stdalign.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/stdarg.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/stdatomic.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/stdbool.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/stddef.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__stddef_max_align_t.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/stdint.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/stdnoreturn.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/tbmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/tgmath.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/tmmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/unwind.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/vadefs.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/vaesintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/varargs.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/vecintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/vpclmulqdqintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/wmmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__wmmintrin_aes.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/__wmmintrin_pclmul.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/x86intrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/xmmintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/xopintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/xsavecintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/xsaveintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/xsaveoptintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/xsavesintrin.h"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/xtestintrin.h"
    "/home/aaa/fp-solver/llvm-6/build/tools/clang/lib/Headers/arm_neon.h"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xclang-headersx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/clang/6.0.0/include/cuda_wrappers" TYPE FILE PERMISSIONS OWNER_READ OWNER_WRITE GROUP_READ WORLD_READ FILES
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/cuda_wrappers/algorithm"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/cuda_wrappers/complex"
    "/home/aaa/fp-solver/llvm-6/tools/clang/lib/Headers/cuda_wrappers/new"
    )
endif()

