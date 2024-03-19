file(REMOVE_RECURSE
  "libRTSanitizerCommon.test.i386.a"
  "libRTSanitizerCommon.test.i386.pdb"
)

# Per-language clean rules from dependency scanning.
foreach(lang ASM CXX)
  include(CMakeFiles/RTSanitizerCommon.test.i386.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
