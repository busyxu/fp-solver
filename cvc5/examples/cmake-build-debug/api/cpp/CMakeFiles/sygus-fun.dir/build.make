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
CMAKE_SOURCE_DIR = /home/aaa/cvc5/examples

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/aaa/cvc5/examples/cmake-build-debug

# Include any dependencies generated for this target.
include api/cpp/CMakeFiles/sygus-fun.dir/depend.make

# Include the progress variables for this target.
include api/cpp/CMakeFiles/sygus-fun.dir/progress.make

# Include the compile flags for this target's objects.
include api/cpp/CMakeFiles/sygus-fun.dir/flags.make

api/cpp/CMakeFiles/sygus-fun.dir/sygus-fun.cpp.o: api/cpp/CMakeFiles/sygus-fun.dir/flags.make
api/cpp/CMakeFiles/sygus-fun.dir/sygus-fun.cpp.o: ../api/cpp/sygus-fun.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/cvc5/examples/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object api/cpp/CMakeFiles/sygus-fun.dir/sygus-fun.cpp.o"
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/sygus-fun.dir/sygus-fun.cpp.o -c /home/aaa/cvc5/examples/api/cpp/sygus-fun.cpp

api/cpp/CMakeFiles/sygus-fun.dir/sygus-fun.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/sygus-fun.dir/sygus-fun.cpp.i"
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/cvc5/examples/api/cpp/sygus-fun.cpp > CMakeFiles/sygus-fun.dir/sygus-fun.cpp.i

api/cpp/CMakeFiles/sygus-fun.dir/sygus-fun.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/sygus-fun.dir/sygus-fun.cpp.s"
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/cvc5/examples/api/cpp/sygus-fun.cpp -o CMakeFiles/sygus-fun.dir/sygus-fun.cpp.s

api/cpp/CMakeFiles/sygus-fun.dir/utils.cpp.o: api/cpp/CMakeFiles/sygus-fun.dir/flags.make
api/cpp/CMakeFiles/sygus-fun.dir/utils.cpp.o: ../api/cpp/utils.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/aaa/cvc5/examples/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object api/cpp/CMakeFiles/sygus-fun.dir/utils.cpp.o"
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/sygus-fun.dir/utils.cpp.o -c /home/aaa/cvc5/examples/api/cpp/utils.cpp

api/cpp/CMakeFiles/sygus-fun.dir/utils.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/sygus-fun.dir/utils.cpp.i"
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/aaa/cvc5/examples/api/cpp/utils.cpp > CMakeFiles/sygus-fun.dir/utils.cpp.i

api/cpp/CMakeFiles/sygus-fun.dir/utils.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/sygus-fun.dir/utils.cpp.s"
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/aaa/cvc5/examples/api/cpp/utils.cpp -o CMakeFiles/sygus-fun.dir/utils.cpp.s

# Object files for target sygus-fun
sygus__fun_OBJECTS = \
"CMakeFiles/sygus-fun.dir/sygus-fun.cpp.o" \
"CMakeFiles/sygus-fun.dir/utils.cpp.o"

# External object files for target sygus-fun
sygus__fun_EXTERNAL_OBJECTS =

bin/api/cpp/sygus-fun: api/cpp/CMakeFiles/sygus-fun.dir/sygus-fun.cpp.o
bin/api/cpp/sygus-fun: api/cpp/CMakeFiles/sygus-fun.dir/utils.cpp.o
bin/api/cpp/sygus-fun: api/cpp/CMakeFiles/sygus-fun.dir/build.make
bin/api/cpp/sygus-fun: api/cpp/CMakeFiles/sygus-fun.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/aaa/cvc5/examples/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Linking CXX executable ../../bin/api/cpp/sygus-fun"
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/sygus-fun.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
api/cpp/CMakeFiles/sygus-fun.dir/build: bin/api/cpp/sygus-fun

.PHONY : api/cpp/CMakeFiles/sygus-fun.dir/build

api/cpp/CMakeFiles/sygus-fun.dir/clean:
	cd /home/aaa/cvc5/examples/cmake-build-debug/api/cpp && $(CMAKE_COMMAND) -P CMakeFiles/sygus-fun.dir/cmake_clean.cmake
.PHONY : api/cpp/CMakeFiles/sygus-fun.dir/clean

api/cpp/CMakeFiles/sygus-fun.dir/depend:
	cd /home/aaa/cvc5/examples/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aaa/cvc5/examples /home/aaa/cvc5/examples/api/cpp /home/aaa/cvc5/examples/cmake-build-debug /home/aaa/cvc5/examples/cmake-build-debug/api/cpp /home/aaa/cvc5/examples/cmake-build-debug/api/cpp/CMakeFiles/sygus-fun.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : api/cpp/CMakeFiles/sygus-fun.dir/depend
