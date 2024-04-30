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
CMAKE_SOURCE_DIR = /home/aaa/fp-solver/z3-4.6.2

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/aaa/fp-solver/z3-4.6.2/build

# Include any dependencies generated for this target.
include src/ast/proofs/CMakeFiles/proofs.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include src/ast/proofs/CMakeFiles/proofs.dir/compiler_depend.make

# Include the progress variables for this target.
include src/ast/proofs/CMakeFiles/proofs.dir/progress.make

# Include the compile flags for this target's objects.
include src/ast/proofs/CMakeFiles/proofs.dir/flags.make

src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.o: src/ast/proofs/CMakeFiles/proofs.dir/flags.make
src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.o: ../src/ast/proofs/proof_checker.cpp
src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.o: src/ast/proofs/CMakeFiles/proofs.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/fp-solver/z3-4.6.2/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.o"
	cd /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.o -MF CMakeFiles/proofs.dir/proof_checker.cpp.o.d -o CMakeFiles/proofs.dir/proof_checker.cpp.o -c /home/aaa/fp-solver/z3-4.6.2/src/ast/proofs/proof_checker.cpp

src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/proofs.dir/proof_checker.cpp.i"
	cd /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/fp-solver/z3-4.6.2/src/ast/proofs/proof_checker.cpp > CMakeFiles/proofs.dir/proof_checker.cpp.i

src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/proofs.dir/proof_checker.cpp.s"
	cd /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/fp-solver/z3-4.6.2/src/ast/proofs/proof_checker.cpp -o CMakeFiles/proofs.dir/proof_checker.cpp.s

src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.o: src/ast/proofs/CMakeFiles/proofs.dir/flags.make
src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.o: ../src/ast/proofs/proof_utils.cpp
src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.o: src/ast/proofs/CMakeFiles/proofs.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/fp-solver/z3-4.6.2/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.o"
	cd /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.o -MF CMakeFiles/proofs.dir/proof_utils.cpp.o.d -o CMakeFiles/proofs.dir/proof_utils.cpp.o -c /home/aaa/fp-solver/z3-4.6.2/src/ast/proofs/proof_utils.cpp

src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/proofs.dir/proof_utils.cpp.i"
	cd /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/fp-solver/z3-4.6.2/src/ast/proofs/proof_utils.cpp > CMakeFiles/proofs.dir/proof_utils.cpp.i

src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/proofs.dir/proof_utils.cpp.s"
	cd /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/fp-solver/z3-4.6.2/src/ast/proofs/proof_utils.cpp -o CMakeFiles/proofs.dir/proof_utils.cpp.s

proofs: src/ast/proofs/CMakeFiles/proofs.dir/proof_checker.cpp.o
proofs: src/ast/proofs/CMakeFiles/proofs.dir/proof_utils.cpp.o
proofs: src/ast/proofs/CMakeFiles/proofs.dir/build.make
.PHONY : proofs

# Rule to build all files generated by this target.
src/ast/proofs/CMakeFiles/proofs.dir/build: proofs
.PHONY : src/ast/proofs/CMakeFiles/proofs.dir/build

src/ast/proofs/CMakeFiles/proofs.dir/clean:
	cd /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs && $(CMAKE_COMMAND) -P CMakeFiles/proofs.dir/cmake_clean.cmake
.PHONY : src/ast/proofs/CMakeFiles/proofs.dir/clean

src/ast/proofs/CMakeFiles/proofs.dir/depend:
	cd /home/aaa/fp-solver/z3-4.6.2/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/fp-solver/z3-4.6.2 /home/aaa/fp-solver/z3-4.6.2/src/ast/proofs /home/aaa/fp-solver/z3-4.6.2/build /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs /home/aaa/fp-solver/z3-4.6.2/build/src/ast/proofs/CMakeFiles/proofs.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/ast/proofs/CMakeFiles/proofs.dir/depend
