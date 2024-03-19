# CMake generated Testfile for 
# Source directory: /home/aaa/cvc5/examples
# Build directory: /home/aaa/cvc5/examples/cmake-build-debug
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(simple_vc_cxx "/home/aaa/cvc5/examples/cmake-build-debug/bin/simple_vc_cxx")
set_tests_properties(simple_vc_cxx PROPERTIES  _BACKTRACE_TRIPLES "/home/aaa/cvc5/examples/CMakeLists.txt;71;add_test;/home/aaa/cvc5/examples/CMakeLists.txt;74;cvc5_add_example;/home/aaa/cvc5/examples/CMakeLists.txt;0;")
add_test(simple_vc_quant_cxx "/home/aaa/cvc5/examples/cmake-build-debug/bin/simple_vc_quant_cxx")
set_tests_properties(simple_vc_quant_cxx PROPERTIES  _BACKTRACE_TRIPLES "/home/aaa/cvc5/examples/CMakeLists.txt;71;add_test;/home/aaa/cvc5/examples/CMakeLists.txt;75;cvc5_add_example;/home/aaa/cvc5/examples/CMakeLists.txt;0;")
subdirs("api/cpp")
