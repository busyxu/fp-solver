file(REMOVE_RECURSE
  "libRTSanitizerCommon.test.x86_64.a"
  "libRTSanitizerCommon.test.x86_64.pdb"
)

# Per-language clean rules from dependency scanning.
foreach(lang ASM CXX)
  include(CMakeFiles/RTSanitizerCommon.test.x86_64.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
