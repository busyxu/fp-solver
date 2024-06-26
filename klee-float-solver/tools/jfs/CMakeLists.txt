#===------------------------------------------------------------------------===#
#
#                                      JFS
#
# Copyright 2017-2018 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#
add_executable(jfs_tool
  main.cpp
)

# Needed for command line support
#jfs_get_llvm_components(llvm_components support)

set(LLVM_COMPONENTS support)
klee_get_llvm_libs(LLVM_LIBS ${LLVM_COMPONENTS})

target_link_libraries(
  jfs_tool
  PRIVATE
  ${LLVM_LIBS}
  JFSSupport
  JFSCore
  JFSTransform
  JFSFuzzingCommon
  JFSFuzzingCommonCmdLine
  JFSZ3Backend
  JFSCXXFuzzingBackend
  JFSCXXFuzzingBackendCmdLine
)

# Give shortname
set_property(TARGET jfs_tool PROPERTY OUTPUT_NAME jfs)
