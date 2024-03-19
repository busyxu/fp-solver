# Install script for directory: /home/aaa/z3-4.6.2/src

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Debug")
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

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  foreach(file
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so.4.6.2.0"
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so.4.6"
      )
    if(EXISTS "${file}" AND
       NOT IS_SYMLINK "${file}")
      file(RPATH_CHECK
           FILE "${file}"
           RPATH "")
    endif()
  endforeach()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE SHARED_LIBRARY FILES
    "/home/aaa/z3-4.6.2/cmake-build-debug/libz3.so.4.6.2.0"
    "/home/aaa/z3-4.6.2/cmake-build-debug/libz3.so.4.6"
    )
  foreach(file
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so.4.6.2.0"
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so.4.6"
      )
    if(EXISTS "${file}" AND
       NOT IS_SYMLINK "${file}")
      if(CMAKE_INSTALL_DO_STRIP)
        execute_process(COMMAND "/usr/bin/strip" "${file}")
      endif()
    endif()
  endforeach()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so")
    file(RPATH_CHECK
         FILE "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so"
         RPATH "")
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE SHARED_LIBRARY FILES "/home/aaa/z3-4.6.2/cmake-build-debug/libz3.so")
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so")
    if(CMAKE_INSTALL_DO_STRIP)
      execute_process(COMMAND "/usr/bin/strip" "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libz3.so")
    endif()
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include" TYPE FILE FILES
    "/home/aaa/z3-4.6.2/src/api/z3_algebraic.h"
    "/home/aaa/z3-4.6.2/src/api/z3_api.h"
    "/home/aaa/z3-4.6.2/src/api/z3_ast_containers.h"
    "/home/aaa/z3-4.6.2/src/api/z3_fixedpoint.h"
    "/home/aaa/z3-4.6.2/src/api/z3_fpa.h"
    "/home/aaa/z3-4.6.2/src/api/z3.h"
    "/home/aaa/z3-4.6.2/src/api/c++/z3++.h"
    "/home/aaa/z3-4.6.2/src/api/z3_interp.h"
    "/home/aaa/z3-4.6.2/src/api/z3_macros.h"
    "/home/aaa/z3-4.6.2/src/api/z3_optimization.h"
    "/home/aaa/z3-4.6.2/src/api/z3_polynomial.h"
    "/home/aaa/z3-4.6.2/src/api/z3_rcf.h"
    "/home/aaa/z3-4.6.2/src/api/z3_v1.h"
    "/home/aaa/z3-4.6.2/src/api/z3_spacer.h"
    )
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/util/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/util/lp/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/polynomial/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/sat/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/nlsat/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/hilbert/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/simplex/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/automata/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/interval/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/realclosure/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/subpaving/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/rewriter/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/normal_forms/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/model/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/substitution/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/parsers/util/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/grobner/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/euclid/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/core/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/sat/tactic/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/arith/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/nlsat/tactic/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/math/subpaving/tactic/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/aig/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/solver/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ackermannization/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/interp/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/cmd_context/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/cmd_context/extra_cmds/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/parsers/smt2/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/proofs/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/fpa/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/pattern/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/ast/rewriter/bit_blaster/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/smt/params/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/smt/proto_model/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/smt/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/bv/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/smt/tactic/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/sls/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/qe/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/duality/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/base/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/dataflow/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/transforms/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/rel/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/pdr/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/clp/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/tab/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/bmc/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/ddnf/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/duality/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/spacer/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/muz/fp/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/nlsat_smt/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/ufbv/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/sat/sat_solver/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/smtlogics/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/fpa/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/opt/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/api/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/api/dll/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/shell/cmake_install.cmake")
  include("/home/aaa/z3-4.6.2/cmake-build-debug/src/test/cmake_install.cmake")

endif()

