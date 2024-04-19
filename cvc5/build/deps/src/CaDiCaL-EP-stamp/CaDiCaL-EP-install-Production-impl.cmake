set(command "/usr/local/bin/cmake;-E;copy;/home/aaa/fp-solver/cvc5/build/deps/src/CaDiCaL-EP/build/libcadical.a;/home/aaa/fp-solver/cvc5/build/deps/lib/libcadical.a")

execute_process(COMMAND ${command} RESULT_VARIABLE result)
if(result)
  set(msg "Command failed (${result}):\n")
  foreach(arg IN LISTS command)
    set(msg "${msg} '${arg}'")
  endforeach()
  message(FATAL_ERROR "${msg}")
endif()
set(command "/usr/local/bin/cmake;-E;copy;/home/aaa/fp-solver/cvc5/build/deps/src/CaDiCaL-EP/src/cadical.hpp;/home/aaa/fp-solver/cvc5/build/deps/include/cadical.hpp")

execute_process(COMMAND ${command} RESULT_VARIABLE result)
if(result)
  set(msg "Command failed (${result}):\n")
  foreach(arg IN LISTS command)
    set(msg "${msg} '${arg}'")
  endforeach()
  message(FATAL_ERROR "${msg}")
endif()
