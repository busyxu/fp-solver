file(REMOVE_RECURSE
  "../../../../lib/clang/6.0.0/lib/linux/libclang_rt.asan-preinit-i386.a"
  "../../../../lib/clang/6.0.0/lib/linux/libclang_rt.asan-preinit-i386.pdb"
)

# Per-language clean rules from dependency scanning.
foreach(lang CXX)
  include(CMakeFiles/clang_rt.asan-preinit-i386.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
