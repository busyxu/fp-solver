# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.23

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
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/aaa/cvc5/examples

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/aaa/cvc5/examples/build

# Include any dependencies generated for this target.
include api/cpp/CMakeFiles/relations.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include api/cpp/CMakeFiles/relations.dir/compiler_depend.make

# Include the progress variables for this target.
include api/cpp/CMakeFiles/relations.dir/progress.make

# Include the compile flags for this target's objects.
include api/cpp/CMakeFiles/relations.dir/flags.make

api/cpp/CMakeFiles/relations.dir/relations.cpp.o: api/cpp/CMakeFiles/relations.dir/flags.make
api/cpp/CMakeFiles/relations.dir/relations.cpp.o: ../api/cpp/relations.cpp
api/cpp/CMakeFiles/relations.dir/relations.cpp.o: api/cpp/CMakeFiles/relations.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/cvc5/examples/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object api/cpp/CMakeFiles/relations.dir/relations.cpp.o"
	cd /home/aaa/cvc5/examples/build/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT api/cpp/CMakeFiles/relations.dir/relations.cpp.o -MF CMakeFiles/relations.dir/relations.cpp.o.d -o CMakeFiles/relations.dir/relations.cpp.o -c /home/aaa/cvc5/examples/api/cpp/relations.cpp

api/cpp/CMakeFiles/relations.dir/relations.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/relations.dir/relations.cpp.i"
	cd /home/aaa/cvc5/examples/build/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/cvc5/examples/api/cpp/relations.cpp > CMakeFiles/relations.dir/relations.cpp.i

api/cpp/CMakeFiles/relations.dir/relations.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/relations.dir/relations.cpp.s"
	cd /home/aaa/cvc5/examples/build/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/cvc5/examples/api/cpp/relations.cpp -o CMakeFiles/relations.dir/relations.cpp.s

# Object files for target relations
relations_OBJECTS = \
"CMakeFiles/relations.dir/relations.cpp.o"

# External object files for target relations
relations_EXTERNAL_OBJECTS =

bin/api/cpp/relations: api/cpp/CMakeFiles/relations.dir/relations.cpp.o
bin/api/cpp/relations: api/cpp/CMakeFiles/relations.dir/build.make
bin/api/cpp/relations: api/cpp/CMakeFiles/relations.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/aaa/cvc5/examples/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable ../../bin/api/cpp/relations"
	cd /home/aaa/cvc5/examples/build/api/cpp && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/relations.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
api/cpp/CMakeFiles/relations.dir/build: bin/api/cpp/relations
.PHONY : api/cpp/CMakeFiles/relations.dir/build

api/cpp/CMakeFiles/relations.dir/clean:
	cd /home/aaa/cvc5/examples/build/api/cpp && $(CMAKE_COMMAND) -P CMakeFiles/relations.dir/cmake_clean.cmake
.PHONY : api/cpp/CMakeFiles/relations.dir/clean

api/cpp/CMakeFiles/relations.dir/depend:
	cd /home/aaa/cvc5/examples/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/cvc5/examples /home/aaa/cvc5/examples/api/cpp /home/aaa/cvc5/examples/build /home/aaa/cvc5/examples/build/api/cpp /home/aaa/cvc5/examples/build/api/cpp/CMakeFiles/relations.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : api/cpp/CMakeFiles/relations.dir/depend
