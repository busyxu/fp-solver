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
include src/opt/CMakeFiles/opt.dir/depend.make

# Include the progress variables for this target.
include src/opt/CMakeFiles/opt.dir/progress.make

# Include the compile flags for this target's objects.
include src/opt/CMakeFiles/opt.dir/flags.make

src/opt/opt_params.hpp: ../scripts/pyg2hpp.py
src/opt/opt_params.hpp: ../scripts/mk_genfile_common.py
src/opt/opt_params.hpp: ../src/opt/opt_params.pyg
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Generating \"/home/aaa/z3-4.6.2/cmake-build-debug/src/opt/opt_params.hpp\" from \"opt_params.pyg\""
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/python3.6 /home/aaa/z3-4.6.2/scripts/pyg2hpp.py /home/aaa/z3-4.6.2/src/opt/opt_params.pyg /home/aaa/z3-4.6.2/cmake-build-debug/src/opt

src/opt/CMakeFiles/opt.dir/maxres.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/maxres.cpp.o: ../src/opt/maxres.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object src/opt/CMakeFiles/opt.dir/maxres.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/maxres.cpp.o -c /home/aaa/z3-4.6.2/src/opt/maxres.cpp

src/opt/CMakeFiles/opt.dir/maxres.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/maxres.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/maxres.cpp > CMakeFiles/opt.dir/maxres.cpp.i

src/opt/CMakeFiles/opt.dir/maxres.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/maxres.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/maxres.cpp -o CMakeFiles/opt.dir/maxres.cpp.s

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o: ../src/opt/maxsmt.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/maxsmt.cpp.o -c /home/aaa/z3-4.6.2/src/opt/maxsmt.cpp

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/maxsmt.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/maxsmt.cpp > CMakeFiles/opt.dir/maxsmt.cpp.i

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/maxsmt.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/maxsmt.cpp -o CMakeFiles/opt.dir/maxsmt.cpp.s

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o: ../src/opt/opt_cmds.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_cmds.cpp.o -c /home/aaa/z3-4.6.2/src/opt/opt_cmds.cpp

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_cmds.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/opt_cmds.cpp > CMakeFiles/opt.dir/opt_cmds.cpp.i

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_cmds.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/opt_cmds.cpp -o CMakeFiles/opt.dir/opt_cmds.cpp.s

src/opt/CMakeFiles/opt.dir/opt_context.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_context.cpp.o: ../src/opt/opt_context.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_context.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_context.cpp.o -c /home/aaa/z3-4.6.2/src/opt/opt_context.cpp

src/opt/CMakeFiles/opt.dir/opt_context.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_context.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/opt_context.cpp > CMakeFiles/opt.dir/opt_context.cpp.i

src/opt/CMakeFiles/opt.dir/opt_context.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_context.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/opt_context.cpp -o CMakeFiles/opt.dir/opt_context.cpp.s

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o: ../src/opt/opt_pareto.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_pareto.cpp.o -c /home/aaa/z3-4.6.2/src/opt/opt_pareto.cpp

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_pareto.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/opt_pareto.cpp > CMakeFiles/opt.dir/opt_pareto.cpp.i

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_pareto.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/opt_pareto.cpp -o CMakeFiles/opt.dir/opt_pareto.cpp.s

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o: ../src/opt/opt_parse.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_parse.cpp.o -c /home/aaa/z3-4.6.2/src/opt/opt_parse.cpp

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_parse.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/opt_parse.cpp > CMakeFiles/opt.dir/opt_parse.cpp.i

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_parse.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/opt_parse.cpp -o CMakeFiles/opt.dir/opt_parse.cpp.s

src/opt/CMakeFiles/opt.dir/optsmt.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/optsmt.cpp.o: ../src/opt/optsmt.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "Building CXX object src/opt/CMakeFiles/opt.dir/optsmt.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/optsmt.cpp.o -c /home/aaa/z3-4.6.2/src/opt/optsmt.cpp

src/opt/CMakeFiles/opt.dir/optsmt.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/optsmt.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/optsmt.cpp > CMakeFiles/opt.dir/optsmt.cpp.i

src/opt/CMakeFiles/opt.dir/optsmt.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/optsmt.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/optsmt.cpp -o CMakeFiles/opt.dir/optsmt.cpp.s

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o: ../src/opt/opt_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_9) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_solver.cpp.o -c /home/aaa/z3-4.6.2/src/opt/opt_solver.cpp

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_solver.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/opt_solver.cpp > CMakeFiles/opt.dir/opt_solver.cpp.i

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_solver.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/opt_solver.cpp -o CMakeFiles/opt.dir/opt_solver.cpp.s

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o: ../src/opt/pb_sls.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_10) "Building CXX object src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/pb_sls.cpp.o -c /home/aaa/z3-4.6.2/src/opt/pb_sls.cpp

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/pb_sls.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/pb_sls.cpp > CMakeFiles/opt.dir/pb_sls.cpp.i

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/pb_sls.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/pb_sls.cpp -o CMakeFiles/opt.dir/pb_sls.cpp.s

src/opt/CMakeFiles/opt.dir/sortmax.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/sortmax.cpp.o: ../src/opt/sortmax.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_11) "Building CXX object src/opt/CMakeFiles/opt.dir/sortmax.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/sortmax.cpp.o -c /home/aaa/z3-4.6.2/src/opt/sortmax.cpp

src/opt/CMakeFiles/opt.dir/sortmax.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/sortmax.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/sortmax.cpp > CMakeFiles/opt.dir/sortmax.cpp.i

src/opt/CMakeFiles/opt.dir/sortmax.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/sortmax.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/sortmax.cpp -o CMakeFiles/opt.dir/sortmax.cpp.s

src/opt/CMakeFiles/opt.dir/wmax.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/wmax.cpp.o: ../src/opt/wmax.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/z3-4.6.2/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_12) "Building CXX object src/opt/CMakeFiles/opt.dir/wmax.cpp.o"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/wmax.cpp.o -c /home/aaa/z3-4.6.2/src/opt/wmax.cpp

src/opt/CMakeFiles/opt.dir/wmax.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/wmax.cpp.i"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/z3-4.6.2/src/opt/wmax.cpp > CMakeFiles/opt.dir/wmax.cpp.i

src/opt/CMakeFiles/opt.dir/wmax.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/wmax.cpp.s"
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/z3-4.6.2/src/opt/wmax.cpp -o CMakeFiles/opt.dir/wmax.cpp.s

opt: src/opt/CMakeFiles/opt.dir/maxres.cpp.o
opt: src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_context.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o
opt: src/opt/CMakeFiles/opt.dir/optsmt.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o
opt: src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o
opt: src/opt/CMakeFiles/opt.dir/sortmax.cpp.o
opt: src/opt/CMakeFiles/opt.dir/wmax.cpp.o
opt: src/opt/CMakeFiles/opt.dir/build.make

.PHONY : opt

# Rule to build all files generated by this target.
src/opt/CMakeFiles/opt.dir/build: opt

.PHONY : src/opt/CMakeFiles/opt.dir/build

src/opt/CMakeFiles/opt.dir/clean:
	cd /home/aaa/z3-4.6.2/cmake-build-debug/src/opt && $(CMAKE_COMMAND) -P CMakeFiles/opt.dir/cmake_clean.cmake
.PHONY : src/opt/CMakeFiles/opt.dir/clean

src/opt/CMakeFiles/opt.dir/depend: src/opt/opt_params.hpp
	cd /home/aaa/z3-4.6.2/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/z3-4.6.2 /home/aaa/z3-4.6.2/src/opt /home/aaa/z3-4.6.2/cmake-build-debug /home/aaa/z3-4.6.2/cmake-build-debug/src/opt /home/aaa/z3-4.6.2/cmake-build-debug/src/opt/CMakeFiles/opt.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/opt/CMakeFiles/opt.dir/depend
