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
include src/tactic/portfolio/CMakeFiles/portfolio.dir/depend.make

# Include the progress variables for this target.
include src/tactic/portfolio/CMakeFiles/portfolio.dir/progress.make

# Include the compile flags for this target's objects.
include src/tactic/portfolio/CMakeFiles/portfolio.dir/flags.make

src/tactic/portfolio/CMakeFiles/portfolio.dir/default_tactic.cpp.o: src/tactic/portfolio/CMakeFiles/portfolio.dir/flags.make
src/tactic/portfolio/CMakeFiles/portfolio.dir/default_tactic.cpp.o: ../src/tactic/portfolio/default_tactic.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/tactic/portfolio/CMakeFiles/portfolio.dir/default_tactic.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/portfolio.dir/default_tactic.cpp.o -c /home/aaa/z3-4.6.2/src/tactic/portfolio/default_tactic.cpp

src/tactic/portfolio/CMakeFiles/portfolio.dir/default_tactic.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/portfolio.dir/default_tactic.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/tactic/portfolio/default_tactic.cpp > CMakeFiles/portfolio.dir/default_tactic.cpp.i

src/tactic/portfolio/CMakeFiles/portfolio.dir/default_tactic.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/portfolio.dir/default_tactic.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/tactic/portfolio/default_tactic.cpp -o CMakeFiles/portfolio.dir/default_tactic.cpp.s

src/tactic/portfolio/CMakeFiles/portfolio.dir/enum2bv_solver.cpp.o: src/tactic/portfolio/CMakeFiles/portfolio.dir/flags.make
src/tactic/portfolio/CMakeFiles/portfolio.dir/enum2bv_solver.cpp.o: ../src/tactic/portfolio/enum2bv_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object src/tactic/portfolio/CMakeFiles/portfolio.dir/enum2bv_solver.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/portfolio.dir/enum2bv_solver.cpp.o -c /home/aaa/z3-4.6.2/src/tactic/portfolio/enum2bv_solver.cpp

src/tactic/portfolio/CMakeFiles/portfolio.dir/enum2bv_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/portfolio.dir/enum2bv_solver.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/tactic/portfolio/enum2bv_solver.cpp > CMakeFiles/portfolio.dir/enum2bv_solver.cpp.i

src/tactic/portfolio/CMakeFiles/portfolio.dir/enum2bv_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/portfolio.dir/enum2bv_solver.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/tactic/portfolio/enum2bv_solver.cpp -o CMakeFiles/portfolio.dir/enum2bv_solver.cpp.s

src/tactic/portfolio/CMakeFiles/portfolio.dir/pb2bv_solver.cpp.o: src/tactic/portfolio/CMakeFiles/portfolio.dir/flags.make
src/tactic/portfolio/CMakeFiles/portfolio.dir/pb2bv_solver.cpp.o: ../src/tactic/portfolio/pb2bv_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object src/tactic/portfolio/CMakeFiles/portfolio.dir/pb2bv_solver.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/portfolio.dir/pb2bv_solver.cpp.o -c /home/aaa/z3-4.6.2/src/tactic/portfolio/pb2bv_solver.cpp

src/tactic/portfolio/CMakeFiles/portfolio.dir/pb2bv_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/portfolio.dir/pb2bv_solver.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/tactic/portfolio/pb2bv_solver.cpp > CMakeFiles/portfolio.dir/pb2bv_solver.cpp.i

src/tactic/portfolio/CMakeFiles/portfolio.dir/pb2bv_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/portfolio.dir/pb2bv_solver.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/tactic/portfolio/pb2bv_solver.cpp -o CMakeFiles/portfolio.dir/pb2bv_solver.cpp.s

src/tactic/portfolio/CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.o: src/tactic/portfolio/CMakeFiles/portfolio.dir/flags.make
src/tactic/portfolio/CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.o: ../src/tactic/portfolio/bounded_int2bv_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object src/tactic/portfolio/CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.o -c /home/aaa/z3-4.6.2/src/tactic/portfolio/bounded_int2bv_solver.cpp

src/tactic/portfolio/CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/tactic/portfolio/bounded_int2bv_solver.cpp > CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.i

src/tactic/portfolio/CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/tactic/portfolio/bounded_int2bv_solver.cpp -o CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.s

src/tactic/portfolio/CMakeFiles/portfolio.dir/fd_solver.cpp.o: src/tactic/portfolio/CMakeFiles/portfolio.dir/flags.make
src/tactic/portfolio/CMakeFiles/portfolio.dir/fd_solver.cpp.o: ../src/tactic/portfolio/fd_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Building CXX object src/tactic/portfolio/CMakeFiles/portfolio.dir/fd_solver.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/portfolio.dir/fd_solver.cpp.o -c /home/aaa/z3-4.6.2/src/tactic/portfolio/fd_solver.cpp

src/tactic/portfolio/CMakeFiles/portfolio.dir/fd_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/portfolio.dir/fd_solver.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/tactic/portfolio/fd_solver.cpp > CMakeFiles/portfolio.dir/fd_solver.cpp.i

src/tactic/portfolio/CMakeFiles/portfolio.dir/fd_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/portfolio.dir/fd_solver.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/tactic/portfolio/fd_solver.cpp -o CMakeFiles/portfolio.dir/fd_solver.cpp.s

src/tactic/portfolio/CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.o: src/tactic/portfolio/CMakeFiles/portfolio.dir/flags.make
src/tactic/portfolio/CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.o: ../src/tactic/portfolio/smt_strategic_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Building CXX object src/tactic/portfolio/CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.o -c /home/aaa/z3-4.6.2/src/tactic/portfolio/smt_strategic_solver.cpp

src/tactic/portfolio/CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/tactic/portfolio/smt_strategic_solver.cpp > CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.i

src/tactic/portfolio/CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/tactic/portfolio/smt_strategic_solver.cpp -o CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.s

portfolio: src/tactic/portfolio/CMakeFiles/portfolio.dir/default_tactic.cpp.o
portfolio: src/tactic/portfolio/CMakeFiles/portfolio.dir/enum2bv_solver.cpp.o
portfolio: src/tactic/portfolio/CMakeFiles/portfolio.dir/pb2bv_solver.cpp.o
portfolio: src/tactic/portfolio/CMakeFiles/portfolio.dir/bounded_int2bv_solver.cpp.o
portfolio: src/tactic/portfolio/CMakeFiles/portfolio.dir/fd_solver.cpp.o
portfolio: src/tactic/portfolio/CMakeFiles/portfolio.dir/smt_strategic_solver.cpp.o
portfolio: src/tactic/portfolio/CMakeFiles/portfolio.dir/build.make

.PHONY : portfolio

# Rule to build all files generated by this target.
src/tactic/portfolio/CMakeFiles/portfolio.dir/build: portfolio

.PHONY : src/tactic/portfolio/CMakeFiles/portfolio.dir/build

src/tactic/portfolio/CMakeFiles/portfolio.dir/clean:
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio && $(CMAKE_COMMAND) -P CMakeFiles/portfolio.dir/cmake_clean.cmake
.PHONY : src/tactic/portfolio/CMakeFiles/portfolio.dir/clean

src/tactic/portfolio/CMakeFiles/portfolio.dir/depend:
	cd /home/aaa/z3-4.6.2/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/z3-4.6.2 /home/aaa/z3-4.6.2/src/tactic/portfolio /home/aaa/z3-4.6.2/cmake-build-debug /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio /home/aaa/z3-4.6.2/cmake-build-debug/src/tactic/portfolio/CMakeFiles/portfolio.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/tactic/portfolio/CMakeFiles/portfolio.dir/depend
