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
include src/parser/CMakeFiles/cvc5parserapi-objs.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include src/parser/CMakeFiles/cvc5parserapi-objs.dir/compiler_depend.make

# Include the progress variables for this target.
include src/parser/CMakeFiles/cvc5parserapi-objs.dir/progress.make

# Include the compile flags for this target's objects.
include src/parser/CMakeFiles/cvc5parserapi-objs.dir/flags.make

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o: src/parser/CMakeFiles/cvc5parserapi-objs.dir/flags.make
src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o: ../src/parser/api/cpp/command.cpp
src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o: src/parser/CMakeFiles/cvc5parserapi-objs.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o -MF CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o.d -o CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o -c /home/aaa/fp-solver/cvc5/src/parser/api/cpp/command.cpp

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.i"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/fp-solver/cvc5/src/parser/api/cpp/command.cpp > CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.i

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.s"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/fp-solver/cvc5/src/parser/api/cpp/command.cpp -o CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.s

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o: src/parser/CMakeFiles/cvc5parserapi-objs.dir/flags.make
src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o: ../src/parser/api/cpp/symbol_manager.cpp
src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o: src/parser/CMakeFiles/cvc5parserapi-objs.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o -MF CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o.d -o CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o -c /home/aaa/fp-solver/cvc5/src/parser/api/cpp/symbol_manager.cpp

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.i"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/fp-solver/cvc5/src/parser/api/cpp/symbol_manager.cpp > CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.i

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.s"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/fp-solver/cvc5/src/parser/api/cpp/symbol_manager.cpp -o CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.s

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o: src/parser/CMakeFiles/cvc5parserapi-objs.dir/flags.make
src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o: ../src/parser/api/cpp/input_parser.cpp
src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o: src/parser/CMakeFiles/cvc5parserapi-objs.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/fp-solver/cvc5/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o -MF CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o.d -o CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o -c /home/aaa/fp-solver/cvc5/src/parser/api/cpp/input_parser.cpp

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.i"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/fp-solver/cvc5/src/parser/api/cpp/input_parser.cpp > CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.i

src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.s"
	cd /home/aaa/fp-solver/cvc5/build/src/parser && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/fp-solver/cvc5/src/parser/api/cpp/input_parser.cpp -o CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.s

cvc5parserapi-objs: src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/command.cpp.o
cvc5parserapi-objs: src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/symbol_manager.cpp.o
cvc5parserapi-objs: src/parser/CMakeFiles/cvc5parserapi-objs.dir/api/cpp/input_parser.cpp.o
cvc5parserapi-objs: src/parser/CMakeFiles/cvc5parserapi-objs.dir/build.make
.PHONY : cvc5parserapi-objs

# Rule to build all files generated by this target.
src/parser/CMakeFiles/cvc5parserapi-objs.dir/build: cvc5parserapi-objs
.PHONY : src/parser/CMakeFiles/cvc5parserapi-objs.dir/build

src/parser/CMakeFiles/cvc5parserapi-objs.dir/clean:
	cd /home/aaa/fp-solver/cvc5/build/src/parser && $(CMAKE_COMMAND) -P CMakeFiles/cvc5parserapi-objs.dir/cmake_clean.cmake
.PHONY : src/parser/CMakeFiles/cvc5parserapi-objs.dir/clean

src/parser/CMakeFiles/cvc5parserapi-objs.dir/depend:
	cd /home/aaa/fp-solver/cvc5/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/fp-solver/cvc5 /home/aaa/fp-solver/cvc5/src/parser /home/aaa/fp-solver/cvc5/build /home/aaa/fp-solver/cvc5/build/src/parser /home/aaa/fp-solver/cvc5/build/src/parser/CMakeFiles/cvc5parserapi-objs.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/parser/CMakeFiles/cvc5parserapi-objs.dir/depend

