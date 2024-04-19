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

# Utility rule file for gen-theory.

# Include any custom commands dependencies for this target.
include src/theory/CMakeFiles/gen-theory.dir/compiler_depend.make

# Include the progress variables for this target.
include src/theory/CMakeFiles/gen-theory.dir/progress.make

src/theory/CMakeFiles/gen-theory: src/theory/type_enumerator.cpp
src/theory/CMakeFiles/gen-theory: src/theory/theory_traits.h
src/theory/CMakeFiles/gen-theory: src/theory/rewriter_tables.h

src/theory/rewriter_tables.h: ../src/theory/mkrewriter
src/theory/rewriter_tables.h: ../src/theory/rewriter_tables_template.h
src/theory/rewriter_tables.h: ../src/theory/builtin/kinds
src/theory/rewriter_tables.h: ../src/theory/booleans/kinds
src/theory/rewriter_tables.h: ../src/theory/uf/kinds
src/theory/rewriter_tables.h: ../src/theory/arith/kinds
src/theory/rewriter_tables.h: ../src/theory/bv/kinds
src/theory/rewriter_tables.h: ../src/theory/ff/kinds
src/theory/rewriter_tables.h: ../src/theory/fp/kinds
src/theory/rewriter_tables.h: ../src/theory/arrays/kinds
src/theory/rewriter_tables.h: ../src/theory/datatypes/kinds
src/theory/rewriter_tables.h: ../src/theory/sep/kinds
src/theory/rewriter_tables.h: ../src/theory/sets/kinds
src/theory/rewriter_tables.h: ../src/theory/bags/kinds
src/theory/rewriter_tables.h: ../src/theory/strings/kinds
src/theory/rewriter_tables.h: ../src/theory/quantifiers/kinds
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Generating rewriter_tables.h"
	cd /home/aaa/fp-solver/cvc5/build/src/theory && ../../../src/theory/mkrewriter /home/aaa/fp-solver/cvc5/src/theory/rewriter_tables_template.h /home/aaa/fp-solver/cvc5/src/theory/builtin/kinds /home/aaa/fp-solver/cvc5/src/theory/booleans/kinds /home/aaa/fp-solver/cvc5/src/theory/uf/kinds /home/aaa/fp-solver/cvc5/src/theory/arith/kinds /home/aaa/fp-solver/cvc5/src/theory/bv/kinds /home/aaa/fp-solver/cvc5/src/theory/ff/kinds /home/aaa/fp-solver/cvc5/src/theory/fp/kinds /home/aaa/fp-solver/cvc5/src/theory/arrays/kinds /home/aaa/fp-solver/cvc5/src/theory/datatypes/kinds /home/aaa/fp-solver/cvc5/src/theory/sep/kinds /home/aaa/fp-solver/cvc5/src/theory/sets/kinds /home/aaa/fp-solver/cvc5/src/theory/bags/kinds /home/aaa/fp-solver/cvc5/src/theory/strings/kinds /home/aaa/fp-solver/cvc5/src/theory/quantifiers/kinds > /home/aaa/fp-solver/cvc5/build/src/theory/rewriter_tables.h

src/theory/theory_traits.h: ../src/theory/mktheorytraits
src/theory/theory_traits.h: ../src/theory/theory_traits_template.h
src/theory/theory_traits.h: ../src/theory/builtin/kinds
src/theory/theory_traits.h: ../src/theory/booleans/kinds
src/theory/theory_traits.h: ../src/theory/uf/kinds
src/theory/theory_traits.h: ../src/theory/arith/kinds
src/theory/theory_traits.h: ../src/theory/bv/kinds
src/theory/theory_traits.h: ../src/theory/ff/kinds
src/theory/theory_traits.h: ../src/theory/fp/kinds
src/theory/theory_traits.h: ../src/theory/arrays/kinds
src/theory/theory_traits.h: ../src/theory/datatypes/kinds
src/theory/theory_traits.h: ../src/theory/sep/kinds
src/theory/theory_traits.h: ../src/theory/sets/kinds
src/theory/theory_traits.h: ../src/theory/bags/kinds
src/theory/theory_traits.h: ../src/theory/strings/kinds
src/theory/theory_traits.h: ../src/theory/quantifiers/kinds
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Generating theory_traits.h"
	cd /home/aaa/fp-solver/cvc5/build/src/theory && ../../../src/theory/mktheorytraits /home/aaa/fp-solver/cvc5/src/theory/theory_traits_template.h /home/aaa/fp-solver/cvc5/src/theory/builtin/kinds /home/aaa/fp-solver/cvc5/src/theory/booleans/kinds /home/aaa/fp-solver/cvc5/src/theory/uf/kinds /home/aaa/fp-solver/cvc5/src/theory/arith/kinds /home/aaa/fp-solver/cvc5/src/theory/bv/kinds /home/aaa/fp-solver/cvc5/src/theory/ff/kinds /home/aaa/fp-solver/cvc5/src/theory/fp/kinds /home/aaa/fp-solver/cvc5/src/theory/arrays/kinds /home/aaa/fp-solver/cvc5/src/theory/datatypes/kinds /home/aaa/fp-solver/cvc5/src/theory/sep/kinds /home/aaa/fp-solver/cvc5/src/theory/sets/kinds /home/aaa/fp-solver/cvc5/src/theory/bags/kinds /home/aaa/fp-solver/cvc5/src/theory/strings/kinds /home/aaa/fp-solver/cvc5/src/theory/quantifiers/kinds > /home/aaa/fp-solver/cvc5/build/src/theory/theory_traits.h

src/theory/type_enumerator.cpp: ../src/theory/mktheorytraits
src/theory/type_enumerator.cpp: ../src/theory/type_enumerator_template.cpp
src/theory/type_enumerator.cpp: ../src/theory/builtin/kinds
src/theory/type_enumerator.cpp: ../src/theory/booleans/kinds
src/theory/type_enumerator.cpp: ../src/theory/uf/kinds
src/theory/type_enumerator.cpp: ../src/theory/arith/kinds
src/theory/type_enumerator.cpp: ../src/theory/bv/kinds
src/theory/type_enumerator.cpp: ../src/theory/ff/kinds
src/theory/type_enumerator.cpp: ../src/theory/fp/kinds
src/theory/type_enumerator.cpp: ../src/theory/arrays/kinds
src/theory/type_enumerator.cpp: ../src/theory/datatypes/kinds
src/theory/type_enumerator.cpp: ../src/theory/sep/kinds
src/theory/type_enumerator.cpp: ../src/theory/sets/kinds
src/theory/type_enumerator.cpp: ../src/theory/bags/kinds
src/theory/type_enumerator.cpp: ../src/theory/strings/kinds
src/theory/type_enumerator.cpp: ../src/theory/quantifiers/kinds
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Generating type_enumerator.cpp"
	cd /home/aaa/fp-solver/cvc5/build/src/theory && ../../../src/theory/mktheorytraits /home/aaa/fp-solver/cvc5/src/theory/type_enumerator_template.cpp /home/aaa/fp-solver/cvc5/src/theory/builtin/kinds /home/aaa/fp-solver/cvc5/src/theory/booleans/kinds /home/aaa/fp-solver/cvc5/src/theory/uf/kinds /home/aaa/fp-solver/cvc5/src/theory/arith/kinds /home/aaa/fp-solver/cvc5/src/theory/bv/kinds /home/aaa/fp-solver/cvc5/src/theory/ff/kinds /home/aaa/fp-solver/cvc5/src/theory/fp/kinds /home/aaa/fp-solver/cvc5/src/theory/arrays/kinds /home/aaa/fp-solver/cvc5/src/theory/datatypes/kinds /home/aaa/fp-solver/cvc5/src/theory/sep/kinds /home/aaa/fp-solver/cvc5/src/theory/sets/kinds /home/aaa/fp-solver/cvc5/src/theory/bags/kinds /home/aaa/fp-solver/cvc5/src/theory/strings/kinds /home/aaa/fp-solver/cvc5/src/theory/quantifiers/kinds > /home/aaa/fp-solver/cvc5/build/src/theory/type_enumerator.cpp

gen-theory: src/theory/CMakeFiles/gen-theory
gen-theory: src/theory/rewriter_tables.h
gen-theory: src/theory/theory_traits.h
gen-theory: src/theory/type_enumerator.cpp
gen-theory: src/theory/CMakeFiles/gen-theory.dir/build.make
.PHONY : gen-theory

# Rule to build all files generated by this target.
src/theory/CMakeFiles/gen-theory.dir/build: gen-theory
.PHONY : src/theory/CMakeFiles/gen-theory.dir/build

src/theory/CMakeFiles/gen-theory.dir/clean:
	cd /home/aaa/fp-solver/cvc5/build/src/theory && $(CMAKE_COMMAND) -P CMakeFiles/gen-theory.dir/cmake_clean.cmake
.PHONY : src/theory/CMakeFiles/gen-theory.dir/clean

src/theory/CMakeFiles/gen-theory.dir/depend:
	cd /home/aaa/fp-solver/cvc5/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/fp-solver/cvc5 /home/aaa/fp-solver/cvc5/src/theory /home/aaa/fp-solver/cvc5/build /home/aaa/fp-solver/cvc5/build/src/theory /home/aaa/fp-solver/cvc5/build/src/theory/CMakeFiles/gen-theory.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/theory/CMakeFiles/gen-theory.dir/depend

