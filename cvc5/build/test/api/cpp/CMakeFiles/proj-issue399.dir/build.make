# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/local/bin/cmake

# The command to remove a file.
RM = /usr/local/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/aaa/fp-solver/cvc5

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/aaa/fp-solver/cvc5/build

# Include any dependencies generated for this target.
include test/api/cpp/CMakeFiles/proj-issue399.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include test/api/cpp/CMakeFiles/proj-issue399.dir/compiler_depend.make

# Include the progress variables for this target.
include test/api/cpp/CMakeFiles/proj-issue399.dir/progress.make

# Include the compile flags for this target's objects.
include test/api/cpp/CMakeFiles/proj-issue399.dir/flags.make

test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o: test/api/cpp/CMakeFiles/proj-issue399.dir/flags.make
test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o: ../test/api/cpp/proj-issue399.cpp
test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o: test/api/cpp/CMakeFiles/proj-issue399.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o -MF CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o.d -o CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o -c /home/aaa/fp-solver/cvc5/test/api/cpp/proj-issue399.cpp

test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/proj-issue399.dir/proj-issue399.cpp.i"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/fp-solver/cvc5/test/api/cpp/proj-issue399.cpp > CMakeFiles/proj-issue399.dir/proj-issue399.cpp.i

test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/proj-issue399.dir/proj-issue399.cpp.s"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/fp-solver/cvc5/test/api/cpp/proj-issue399.cpp -o CMakeFiles/proj-issue399.dir/proj-issue399.cpp.s

# Object files for target proj-issue399
proj__issue399_OBJECTS = \
"CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o"

# External object files for target proj-issue399
proj__issue399_EXTERNAL_OBJECTS =

bin/test/api/cpp/proj-issue399: test/api/cpp/CMakeFiles/proj-issue399.dir/proj-issue399.cpp.o
bin/test/api/cpp/proj-issue399: test/api/cpp/CMakeFiles/proj-issue399.dir/build.make
bin/test/api/cpp/proj-issue399: src/main/libmain-test.so
bin/test/api/cpp/proj-issue399: src/parser/libcvc5parser.so.1
bin/test/api/cpp/proj-issue399: src/libcvc5.so.1
bin/test/api/cpp/proj-issue399: deps/lib/libpolyxx.so
bin/test/api/cpp/proj-issue399: deps/lib/libpoly.so
bin/test/api/cpp/proj-issue399: /usr/local/lib/libgmp.so
bin/test/api/cpp/proj-issue399: test/api/cpp/CMakeFiles/proj-issue399.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable ../../../bin/test/api/cpp/proj-issue399"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/proj-issue399.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
test/api/cpp/CMakeFiles/proj-issue399.dir/build: bin/test/api/cpp/proj-issue399
.PHONY : test/api/cpp/CMakeFiles/proj-issue399.dir/build

test/api/cpp/CMakeFiles/proj-issue399.dir/clean:
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && $(CMAKE_COMMAND) -P CMakeFiles/proj-issue399.dir/cmake_clean.cmake
.PHONY : test/api/cpp/CMakeFiles/proj-issue399.dir/clean

test/api/cpp/CMakeFiles/proj-issue399.dir/depend:
	cd /home/aaa/fp-solver/cvc5/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/fp-solver/cvc5 /home/aaa/fp-solver/cvc5/test/api/cpp /home/aaa/fp-solver/cvc5/build /home/aaa/fp-solver/cvc5/build/test/api/cpp /home/aaa/fp-solver/cvc5/build/test/api/cpp/CMakeFiles/proj-issue399.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : test/api/cpp/CMakeFiles/proj-issue399.dir/depend

