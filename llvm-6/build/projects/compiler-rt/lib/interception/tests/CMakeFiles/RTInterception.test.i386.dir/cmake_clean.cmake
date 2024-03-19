file(REMOVE_RECURSE
  "libRTInterception.test.i386.a"
  "libRTInterception.test.i386.pdb"
)

# Per-language clean rules from dependency scanning.
foreach(lang CXX)
  include(CMakeFiles/RTInterception.test.i386.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
