/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A multi-precision integer constant.
 */

// these gestures are used to avoid a public header dependence on base/cvc5config.h

#if 0
#  define CVC5_NEED_INT64_T_OVERLOADS
#endif

#if /* use CLN */ 0
#  define CVC5_CLN_IMP
#endif /* 0 */
#if /* use GMP */ 1
#  define CVC5_GMP_IMP
#endif /* 1 */

#ifdef CVC5_CLN_IMP
#  include "util/integer_cln_imp.h"
#endif /* CVC5_CLN_IMP */

#ifdef CVC5_GMP_IMP
#  include "util/integer_gmp_imp.h"
#endif /* CVC5_GMP_IMP */
