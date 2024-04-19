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

# Utility rule file for regress-lfsc.

# Include any custom commands dependencies for this target.
include test/regress/cli/CMakeFiles/regress-lfsc.dir/compiler_depend.make

# Include the progress variables for this target.
include test/regress/cli/CMakeFiles/regress-lfsc.dir/progress.make

test/regress/cli/CMakeFiles/regress-lfsc:
	cd /home/aaa/fp-solver/cvc5/build/test/regress/cli && /usr/local/bin/cmake -E env RUN_REGRESSION_ARGS='--tester lfsc' ctest --output-on-failure -L regress[0-2] -j16 $$ARGS

regress-lfsc: test/regress/cli/CMakeFiles/regress-lfsc
regress-lfsc: test/regress/cli/CMakeFiles/regress-lfsc.dir/build.make
.PHONY : regress-lfsc

# Rule to build all files generated by this target.
test/regress/cli/CMakeFiles/regress-lfsc.dir/build: regress-lfsc
.PHONY : test/regress/cli/CMakeFiles/regress-lfsc.dir/build

test/regress/cli/CMakeFiles/regress-lfsc.dir/clean:
	cd /home/aaa/fp-solver/cvc5/build/test/regress/cli && $(CMAKE_COMMAND) -P CMakeFiles/regress-lfsc.dir/cmake_clean.cmake
.PHONY : test/regress/cli/CMakeFiles/regress-lfsc.dir/clean

test/regress/cli/CMakeFiles/regress-lfsc.dir/depend:
	cd /home/aaa/fp-solver/cvc5/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/fp-solver/cvc5 /home/aaa/fp-solver/cvc5/test/regress/cli /home/aaa/fp-solver/cvc5/build /home/aaa/fp-solver/cvc5/build/test/regress/cli /home/aaa/fp-solver/cvc5/build/test/regress/cli/CMakeFiles/regress-lfsc.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : test/regress/cli/CMakeFiles/regress-lfsc.dir/depend

