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

# Utility rule file for ANTLR3-EP-jar.

# Include any custom commands dependencies for this target.
include src/parser/CMakeFiles/ANTLR3-EP-jar.dir/compiler_depend.make

# Include the progress variables for this target.
include src/parser/CMakeFiles/ANTLR3-EP-jar.dir/progress.make

src/parser/CMakeFiles/ANTLR3-EP-jar: src/parser/CMakeFiles/ANTLR3-EP-jar-complete

src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-install
src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-mkdir
src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-download
src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-update
src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-patch
src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-configure
src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-build
src/parser/CMakeFiles/ANTLR3-EP-jar-complete: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-install
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Completed 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/src/parser/CMakeFiles
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/src/parser/CMakeFiles/ANTLR3-EP-jar-complete
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-done

deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-build: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-configure
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "No build step for 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-build && /usr/local/bin/cmake -E echo_append
	cd /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-build && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-build

deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-configure: deps/tmp/ANTLR3-EP-jar-cfgcmd.txt
deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-configure: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-patch
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "No configure step for 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-build && /usr/local/bin/cmake -E echo_append
	cd /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-build && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-configure

deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-download: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-urlinfo.txt
deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-download: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-mkdir
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Performing download step (download and verify) for 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/deps/src && /usr/local/bin/cmake -P /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-download-Production.cmake
	cd /home/aaa/fp-solver/cvc5/build/deps/src && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-download

deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-install: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-build
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Performing install step for 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-build && /usr/local/bin/cmake -P /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-install-Production.cmake
	cd /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-build && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-install

deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-mkdir:
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Creating directories for 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-build
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/deps
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/deps/tmp
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/deps/src
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E make_directory /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-mkdir

deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-patch: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-update
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "No patch step for 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E echo_append
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-patch

deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-update: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-download
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "No update step for 'ANTLR3-EP-jar'"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E echo_append
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/local/bin/cmake -E touch /home/aaa/fp-solver/cvc5/build/deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-update

ANTLR3-EP-jar: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-build
ANTLR3-EP-jar: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-configure
ANTLR3-EP-jar: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-download
ANTLR3-EP-jar: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-install
ANTLR3-EP-jar: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-mkdir
ANTLR3-EP-jar: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-patch
ANTLR3-EP-jar: deps/src/ANTLR3-EP-jar-stamp/ANTLR3-EP-jar-update
ANTLR3-EP-jar: src/parser/CMakeFiles/ANTLR3-EP-jar
ANTLR3-EP-jar: src/parser/CMakeFiles/ANTLR3-EP-jar-complete
ANTLR3-EP-jar: src/parser/CMakeFiles/ANTLR3-EP-jar.dir/build.make
.PHONY : ANTLR3-EP-jar

# Rule to build all files generated by this target.
src/parser/CMakeFiles/ANTLR3-EP-jar.dir/build: ANTLR3-EP-jar
.PHONY : src/parser/CMakeFiles/ANTLR3-EP-jar.dir/build

src/parser/CMakeFiles/ANTLR3-EP-jar.dir/clean:
	cd /home/aaa/fp-solver/cvc5/build/src/parser && $(CMAKE_COMMAND) -P CMakeFiles/ANTLR3-EP-jar.dir/cmake_clean.cmake
.PHONY : src/parser/CMakeFiles/ANTLR3-EP-jar.dir/clean

src/parser/CMakeFiles/ANTLR3-EP-jar.dir/depend:
	cd /home/aaa/fp-solver/cvc5/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/fp-solver/cvc5 /home/aaa/fp-solver/cvc5/src/parser /home/aaa/fp-solver/cvc5/build /home/aaa/fp-solver/cvc5/build/src/parser /home/aaa/fp-solver/cvc5/build/src/parser/CMakeFiles/ANTLR3-EP-jar.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/parser/CMakeFiles/ANTLR3-EP-jar.dir/depend

