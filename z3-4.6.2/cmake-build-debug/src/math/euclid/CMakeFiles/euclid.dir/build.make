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
include src/math/euclid/CMakeFiles/euclid.dir/depend.make

# Include the progress variables for this target.
include src/math/euclid/CMakeFiles/euclid.dir/progress.make

# Include the compile flags for this target's objects.
include src/math/euclid/CMakeFiles/euclid.dir/flags.make

src/math/euclid/CMakeFiles/euclid.dir/euclidean_solver.cpp.o: src/math/euclid/CMakeFiles/euclid.dir/flags.make
src/math/euclid/CMakeFiles/euclid.dir/euclidean_solver.cpp.o: ../src/math/euclid/euclidean_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/math/euclid/CMakeFiles/euclid.dir/euclidean_solver.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/math/euclid && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/euclid.dir/euclidean_solver.cpp.o -c /home/aaa/z3-4.6.2/src/math/euclid/euclidean_solver.cpp

src/math/euclid/CMakeFiles/euclid.dir/euclidean_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/euclid.dir/euclidean_solver.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/math/euclid && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/math/euclid/euclidean_solver.cpp > CMakeFiles/euclid.dir/euclidean_solver.cpp.i

src/math/euclid/CMakeFiles/euclid.dir/euclidean_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/euclid.dir/euclidean_solver.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/math/euclid && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/math/euclid/euclidean_solver.cpp -o CMakeFiles/euclid.dir/euclidean_solver.cpp.s

euclid: src/math/euclid/CMakeFiles/euclid.dir/euclidean_solver.cpp.o
euclid: src/math/euclid/CMakeFiles/euclid.dir/build.make

.PHONY : euclid

# Rule to build all files generated by this target.
src/math/euclid/CMakeFiles/euclid.dir/build: euclid

.PHONY : src/math/euclid/CMakeFiles/euclid.dir/build

src/math/euclid/CMakeFiles/euclid.dir/clean:
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/math/euclid && $(CMAKE_COMMAND) -P CMakeFiles/euclid.dir/cmake_clean.cmake
.PHONY : src/math/euclid/CMakeFiles/euclid.dir/clean

src/math/euclid/CMakeFiles/euclid.dir/depend:
	cd /home/aaa/z3-4.6.2/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/z3-4.6.2 /home/aaa/z3-4.6.2/src/math/euclid /home/aaa/z3-4.6.2/cmake-build-debug /home/aaa/z3-4.6.2/cmake-build-debug/src/math/euclid /home/aaa/z3-4.6.2/cmake-build-debug/src/math/euclid/CMakeFiles/euclid.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/math/euclid/CMakeFiles/euclid.dir/depend
