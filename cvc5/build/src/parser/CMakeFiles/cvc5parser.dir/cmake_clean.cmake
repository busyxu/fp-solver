file(REMOVE_RECURSE
  "libcvc5parser.pdb"
  "libcvc5parser.so"
  "libcvc5parser.so.1"
)

# Per-language clean rules from dependency scanning.
foreach(lang CXX)
  include(CMakeFiles/cvc5parser.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
