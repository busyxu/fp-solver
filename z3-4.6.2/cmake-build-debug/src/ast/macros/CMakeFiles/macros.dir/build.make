# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.17

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

# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /home/aaa/Desktop/clion-2020.3.2/bin/cmake/linux/bin/cmake

# The command to remove a file.
RM = /home/aaa/Desktop/clion-2020.3.2/bin/cmake/linux/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/aaa/z3-4.6.2

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/aaa/z3-4.6.2/cmake-build-debug

# Include any dependencies generated for this target.
include src/ast/macros/CMakeFiles/macros.dir/depend.make

# Include the progress variables for this target.
include src/ast/macros/CMakeFiles/macros.dir/progress.make

# Include the compile flags for this target's objects.
include src/ast/macros/CMakeFiles/macros.dir/flags.make

src/ast/macros/CMakeFiles/macros.dir/macro_finder.cpp.o: src/ast/macros/CMakeFiles/macros.dir/flags.make
src/ast/macros/CMakeFiles/macros.dir/macro_finder.cpp.o: ../src/ast/macros/macro_finder.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/ast/macros/CMakeFiles/macros.dir/macro_finder.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/macros.dir/macro_finder.cpp.o -c /home/aaa/z3-4.6.2/src/ast/macros/macro_finder.cpp

src/ast/macros/CMakeFiles/macros.dir/macro_finder.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/macros.dir/macro_finder.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/ast/macros/macro_finder.cpp > CMakeFiles/macros.dir/macro_finder.cpp.i

src/ast/macros/CMakeFiles/macros.dir/macro_finder.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/macros.dir/macro_finder.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/ast/macros/macro_finder.cpp -o CMakeFiles/macros.dir/macro_finder.cpp.s

src/ast/macros/CMakeFiles/macros.dir/macro_manager.cpp.o: src/ast/macros/CMakeFiles/macros.dir/flags.make
src/ast/macros/CMakeFiles/macros.dir/macro_manager.cpp.o: ../src/ast/macros/macro_manager.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object src/ast/macros/CMakeFiles/macros.dir/macro_manager.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/macros.dir/macro_manager.cpp.o -c /home/aaa/z3-4.6.2/src/ast/macros/macro_manager.cpp

src/ast/macros/CMakeFiles/macros.dir/macro_manager.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/macros.dir/macro_manager.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/ast/macros/macro_manager.cpp > CMakeFiles/macros.dir/macro_manager.cpp.i

src/ast/macros/CMakeFiles/macros.dir/macro_manager.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/macros.dir/macro_manager.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/ast/macros/macro_manager.cpp -o CMakeFiles/macros.dir/macro_manager.cpp.s

src/ast/macros/CMakeFiles/macros.dir/macro_util.cpp.o: src/ast/macros/CMakeFiles/macros.dir/flags.make
src/ast/macros/CMakeFiles/macros.dir/macro_util.cpp.o: ../src/ast/macros/macro_util.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object src/ast/macros/CMakeFiles/macros.dir/macro_util.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/macros.dir/macro_util.cpp.o -c /home/aaa/z3-4.6.2/src/ast/macros/macro_util.cpp

src/ast/macros/CMakeFiles/macros.dir/macro_util.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/macros.dir/macro_util.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/ast/macros/macro_util.cpp > CMakeFiles/macros.dir/macro_util.cpp.i

src/ast/macros/CMakeFiles/macros.dir/macro_util.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/macros.dir/macro_util.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/ast/macros/macro_util.cpp -o CMakeFiles/macros.dir/macro_util.cpp.s

src/ast/macros/CMakeFiles/macros.dir/quasi_macros.cpp.o: src/ast/macros/CMakeFiles/macros.dir/flags.make
src/ast/macros/CMakeFiles/macros.dir/quasi_macros.cpp.o: ../src/ast/macros/quasi_macros.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object src/ast/macros/CMakeFiles/macros.dir/quasi_macros.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/macros.dir/quasi_macros.cpp.o -c /home/aaa/z3-4.6.2/src/ast/macros/quasi_macros.cpp

src/ast/macros/CMakeFiles/macros.dir/quasi_macros.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/macros.dir/quasi_macros.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/ast/macros/quasi_macros.cpp > CMakeFiles/macros.dir/quasi_macros.cpp.i

src/ast/macros/CMakeFiles/macros.dir/quasi_macros.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/macros.dir/quasi_macros.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/ast/macros/quasi_macros.cpp -o CMakeFiles/macros.dir/quasi_macros.cpp.s

macros: src/ast/macros/CMakeFiles/macros.dir/macro_finder.cpp.o
macros: src/ast/macros/CMakeFiles/macros.dir/macro_manager.cpp.o
macros: src/ast/macros/CMakeFiles/macros.dir/macro_util.cpp.o
macros: src/ast/macros/CMakeFiles/macros.dir/quasi_macros.cpp.o
macros: src/ast/macros/CMakeFiles/macros.dir/build.make

.PHONY : macros

# Rule to build all files generated by this target.
src/ast/macros/CMakeFiles/macros.dir/build: macros

.PHONY : src/ast/macros/CMakeFiles/macros.dir/build

src/ast/macros/CMakeFiles/macros.dir/clean:
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros && $(CMAKE_COMMAND) -P CMakeFiles/macros.dir/cmake_clean.cmake
.PHONY : src/ast/macros/CMakeFiles/macros.dir/clean

src/ast/macros/CMakeFiles/macros.dir/depend:
	cd /home/aaa/z3-4.6.2/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/z3-4.6.2 /home/aaa/z3-4.6.2/src/ast/macros /home/aaa/z3-4.6.2/cmake-build-debug /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros /home/aaa/z3-4.6.2/cmake-build-debug/src/ast/macros/CMakeFiles/macros.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/ast/macros/CMakeFiles/macros.dir/depend
