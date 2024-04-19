###############################################################################
# Top contributors (to current version):
#   Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
# Configuration file for the generation of cmake dependency graphs of cmake
# targets.
##

set(CTX "/home/aaa/fp-solver/cvc5/build/src/context/CMakeFiles/cvc5base.dir/")
set(BASE "/home/aaa/fp-solver/cvc5/build/src/base/CMakeFiles/cvc5base.dir/")

# ignore targets that do not actually help the understanding or are (usually)
# not interesting: tests and object files.
set(GRAPHVIZ_IGNORE_TARGETS 
    main-test
    boilerplate issue4889 issue5074 issue6111 ouroborous proj-issue306 proj-issue334 proj-issue344 proj-issue345 proj-issue377 proj-issue388 proj-issue395 proj-issue399 proj-issue418 proj-issue421 proj-issue445 proj-issue455 proj-issue484 reset_assertions sep_log_api smt2_compliance testyx two_solvers
    ${CTX}context.cpp.o ${CTX}context_mm.cpp.o
    ${BASE}check.cpp.o ${BASE}configuration.cpp.o ${BASE}exception.cpp.o
    ${BASE}git_versioninfo.cpp.o ${BASE}listener.cpp.o ${BASE}output.cpp.o
)
set(GRAPHVIZ_GENERATE_DEPENDERS FALSE)
