file(REMOVE_RECURSE
  "libcvc5.pdb"
  "libcvc5.so"
  "libcvc5.so.1"
)

# Per-language clean rules from dependency scanning.
foreach(lang C CXX)
  include(CMakeFiles/cvc5.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
