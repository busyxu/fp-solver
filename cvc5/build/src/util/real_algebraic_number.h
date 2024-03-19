/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A real algebraic number constant.
 */

// these gestures are used to avoid a public header dependence on base/cvc5config.h

#if /* use libpoly */ 1
#  define CVC5_POLY_IMP
#endif /* 1 */

#include "util/real_algebraic_number_poly_imp.h"
