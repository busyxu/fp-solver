# Install script for directory: /home/aaa/fp-solver/llvm-6/tools/clang/tools/extra/clang-tidy

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

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xclangTidyx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/home/aaa/fp-solver/llvm-6/build/lib/libclangTidy.a")
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/android/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/boost/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/bugprone/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/cert/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/cppcoreguidelines/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/fuchsia/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/google/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/hicpp/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/llvm/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/misc/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/modernize/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/mpi/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/objc/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/performance/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/plugin/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/readability/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/tool/cmake_install.cmake")
  include("/home/aaa/fp-solver/llvm-6/build/tools/clang/tools/extra/clang-tidy/utils/cmake_install.cmake")

endif()

