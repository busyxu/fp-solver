#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_subdirectory(gen-bout)
add_subdirectory(gen-random-bout)
add_subdirectory(kleaver)
add_subdirectory(klee)
add_subdirectory(klee-replay)
add_subdirectory(klee-stats)
add_subdirectory(klee-zesti)
add_subdirectory(ktest-tool)

# add by zgf
#add_subdirectory(FunctionTypeExtractor)
add_subdirectory(jfs)
add_subdirectory(jfs-smt2cxx)
