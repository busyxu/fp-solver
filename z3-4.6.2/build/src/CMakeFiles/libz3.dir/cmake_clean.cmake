file(REMOVE_RECURSE
  "../libz3.pdb"
  "../libz3.so"
  "../libz3.so.4.6"
  "../libz3.so.4.6.2.0"
)

# Per-language clean rules from dependency scanning.
foreach(lang CXX)
  include(CMakeFiles/libz3.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
