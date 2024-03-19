/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 */

#ifndef CVC5__BASE__CVC5CONFIG_H
#define CVC5__BASE__CVC5CONFIG_H

/* Full name of this package. */
#define CVC5_PACKAGE_NAME "cvc5"

/* Define to 1 if cvc5 is built with (optional) GPLed library dependencies. */
#define CVC5_GPL_DEPS 0

/* Define to use the CLN multi-precision arithmetic library. */
/* #undef CVC5_CLN_IMP */

/* Define to use the GMP multi-precision arithmetic library. */
#define CVC5_GMP_IMP

/* Define to use the libpoly polynomial library. */
#define CVC5_POLY_IMP

/* Define to 1 if Boost threading library has support for thread attributes. */
#define BOOST_HAS_THREAD_ATTR 0

/* Define if `clock_gettime' is supported by the platform. */
#define HAVE_CLOCK_GETTIME

/* Define to 1 if the declaration of `optreset' is available. */
#define HAVE_DECL_OPTRESET 0

/* Define to 1 if the <ext/stdio_filebuf.h> header file is available. */
#define HAVE_EXT_STDIO_FILEBUF_H 1

/* Define if `ffs' is supported by the platform. */
#define HAVE_FFS

/* Define to 1 to use libedit. */
#define HAVE_LIBEDITLINE 0

/* Define to 1 if `rl_completion_entry_function' returns (char *). */
#define EDITLINE_COMPENTRY_FUNC_RETURNS_CHARP 0

/* Define if `sigaltstack' is supported by the platform. */
#define HAVE_SIGALTSTACK

/* Define to 1 if `strerror_r' is supported by the platform. */
#define HAVE_STRERROR_R 1

/* Define if `strtok_r' is supported by the platform. */
#define HAVE_STRTOK_R

/* Define if `setitimer` is supported by the platform. */
#define HAVE_SETITIMER 1

/* Define to 1 if the <unistd.h> header file is available. */
#define HAVE_UNISTD_H 1

/* Define to 1 if the <sys/wait.h> header file is available. */
#define HAVE_SYS_WAIT_H 1

/* Define to 1 if `strerror_r' returns (char *). */
#define STRERROR_R_CHAR_P 0

#define CVC5_STATIC_BUILD 0

#endif /* __CVC5__CVC5AUTOCONFIG_H */
