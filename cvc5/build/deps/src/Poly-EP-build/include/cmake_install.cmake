# Install script for directory: /home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/home/aaa/fp-solver/cvc5/build/deps")
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

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/poly" TYPE FILE FILES
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/algebraic_number.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/assignment.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/dyadic_interval.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/dyadic_rational.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/feasibility_set.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/integer.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/interval.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/monomial.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/output_language.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/poly.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polynomial.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polynomial_context.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polynomial_hash_set.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polynomial_vector.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/rational.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/rational_interval.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/sign_condition.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/upolynomial.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/upolynomial_factors.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/value.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/variable_db.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/variable_list.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/variable_order.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/version.h"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/poly/polyxx" TYPE FILE FILES
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/algebraic_number.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/assignment.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/context.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/dyadic_interval.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/dyadic_rational.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/integer.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/integer_ring.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/interval.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/interval_assignment.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/polynomial.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/polynomial_utils.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/rational.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/rational_interval.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/sign_condition.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/upolynomial.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/utils.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/value.h"
    "/home/aaa/fp-solver/cvc5/build/deps/src/Poly-EP/include/polyxx/variable.h"
    )
endif()

