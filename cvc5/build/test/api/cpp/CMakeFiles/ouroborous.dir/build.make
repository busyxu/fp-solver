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
include test/api/cpp/CMakeFiles/ouroborous.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include test/api/cpp/CMakeFiles/ouroborous.dir/compiler_depend.make

# Include the progress variables for this target.
include test/api/cpp/CMakeFiles/ouroborous.dir/progress.make

# Include the compile flags for this target's objects.
include test/api/cpp/CMakeFiles/ouroborous.dir/flags.make

test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.o: test/api/cpp/CMakeFiles/ouroborous.dir/flags.make
test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.o: ../test/api/cpp/ouroborous.cpp
test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.o: test/api/cpp/CMakeFiles/ouroborous.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.o"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.o -MF CMakeFiles/ouroborous.dir/ouroborous.cpp.o.d -o CMakeFiles/ouroborous.dir/ouroborous.cpp.o -c /home/aaa/fp-solver/cvc5/test/api/cpp/ouroborous.cpp

test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/ouroborous.dir/ouroborous.cpp.i"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/fp-solver/cvc5/test/api/cpp/ouroborous.cpp > CMakeFiles/ouroborous.dir/ouroborous.cpp.i

test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/ouroborous.dir/ouroborous.cpp.s"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/fp-solver/cvc5/test/api/cpp/ouroborous.cpp -o CMakeFiles/ouroborous.dir/ouroborous.cpp.s

# Object files for target ouroborous
ouroborous_OBJECTS = \
"CMakeFiles/ouroborous.dir/ouroborous.cpp.o"

# External object files for target ouroborous
ouroborous_EXTERNAL_OBJECTS =

bin/test/api/cpp/ouroborous: test/api/cpp/CMakeFiles/ouroborous.dir/ouroborous.cpp.o
bin/test/api/cpp/ouroborous: test/api/cpp/CMakeFiles/ouroborous.dir/build.make
bin/test/api/cpp/ouroborous: src/main/libmain-test.so
bin/test/api/cpp/ouroborous: src/parser/libcvc5parser.so.1
bin/test/api/cpp/ouroborous: src/libcvc5.so.1
bin/test/api/cpp/ouroborous: deps/lib/libpolyxx.so
bin/test/api/cpp/ouroborous: deps/lib/libpoly.so
bin/test/api/cpp/ouroborous: /usr/local/lib/libgmp.so
bin/test/api/cpp/ouroborous: test/api/cpp/CMakeFiles/ouroborous.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable ../../../bin/test/api/cpp/ouroborous"
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/ouroborous.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
test/api/cpp/CMakeFiles/ouroborous.dir/build: bin/test/api/cpp/ouroborous
.PHONY : test/api/cpp/CMakeFiles/ouroborous.dir/build

test/api/cpp/CMakeFiles/ouroborous.dir/clean:
	cd /home/aaa/fp-solver/cvc5/build/test/api/cpp && $(CMAKE_COMMAND) -P CMakeFiles/ouroborous.dir/cmake_clean.cmake
.PHONY : test/api/cpp/CMakeFiles/ouroborous.dir/clean

test/api/cpp/CMakeFiles/ouroborous.dir/depend:
	cd /home/aaa/fp-solver/cvc5/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/fp-solver/cvc5 /home/aaa/fp-solver/cvc5/test/api/cpp /home/aaa/fp-solver/cvc5/build /home/aaa/fp-solver/cvc5/build/test/api/cpp /home/aaa/fp-solver/cvc5/build/test/api/cpp/CMakeFiles/ouroborous.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : test/api/cpp/CMakeFiles/ouroborous.dir/depend

