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
include src/muz/ddnf/CMakeFiles/ddnf.dir/depend.make

# Include the progress variables for this target.
include src/muz/ddnf/CMakeFiles/ddnf.dir/progress.make

# Include the compile flags for this target's objects.
include src/muz/ddnf/CMakeFiles/ddnf.dir/flags.make

src/muz/ddnf/CMakeFiles/ddnf.dir/ddnf.cpp.o: src/muz/ddnf/CMakeFiles/ddnf.dir/flags.make
src/muz/ddnf/CMakeFiles/ddnf.dir/ddnf.cpp.o: ../src/muz/ddnf/ddnf.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/muz/ddnf/CMakeFiles/ddnf.dir/ddnf.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/muz/ddnf && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/ddnf.dir/ddnf.cpp.o -c /home/aaa/z3-4.6.2/src/muz/ddnf/ddnf.cpp

src/muz/ddnf/CMakeFiles/ddnf.dir/ddnf.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/ddnf.dir/ddnf.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/muz/ddnf && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/muz/ddnf/ddnf.cpp > CMakeFiles/ddnf.dir/ddnf.cpp.i

src/muz/ddnf/CMakeFiles/ddnf.dir/ddnf.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/ddnf.dir/ddnf.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/muz/ddnf && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/muz/ddnf/ddnf.cpp -o CMakeFiles/ddnf.dir/ddnf.cpp.s

ddnf: src/muz/ddnf/CMakeFiles/ddnf.dir/ddnf.cpp.o
ddnf: src/muz/ddnf/CMakeFiles/ddnf.dir/build.make

.PHONY : ddnf

# Rule to build all files generated by this target.
src/muz/ddnf/CMakeFiles/ddnf.dir/build: ddnf

.PHONY : src/muz/ddnf/CMakeFiles/ddnf.dir/build

src/muz/ddnf/CMakeFiles/ddnf.dir/clean:
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/muz/ddnf && $(CMAKE_COMMAND) -P CMakeFiles/ddnf.dir/cmake_clean.cmake
.PHONY : src/muz/ddnf/CMakeFiles/ddnf.dir/clean

src/muz/ddnf/CMakeFiles/ddnf.dir/depend:
	cd /home/aaa/z3-4.6.2/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/z3-4.6.2 /home/aaa/z3-4.6.2/src/muz/ddnf /home/aaa/z3-4.6.2/cmake-build-debug /home/aaa/z3-4.6.2/cmake-build-debug/src/muz/ddnf /home/aaa/z3-4.6.2/cmake-build-debug/src/muz/ddnf/CMakeFiles/ddnf.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/muz/ddnf/CMakeFiles/ddnf.dir/depend
