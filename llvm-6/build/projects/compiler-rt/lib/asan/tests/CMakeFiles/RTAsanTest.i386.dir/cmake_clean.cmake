file(REMOVE_RECURSE
  "libRTAsanTest.i386.a"
  "libRTAsanTest.i386.pdb"
)

# Per-language clean rules from dependency scanning.
foreach(lang ASM CXX)
  include(CMakeFiles/RTAsanTest.i386.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
