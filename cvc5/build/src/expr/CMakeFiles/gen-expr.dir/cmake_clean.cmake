file(REMOVE_RECURSE
  "CMakeFiles/gen-expr"
  "kind.cpp"
  "kind.h"
  "metakind.cpp"
  "metakind.h"
  "node_manager.cpp"
  "node_manager.h"
  "type_checker.cpp"
  "type_properties.cpp"
  "type_properties.h"
)

# Per-language clean rules from dependency scanning.
foreach(lang )
  include(CMakeFiles/gen-expr.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
