/*=====add by yx =====*/
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  double a[] = { 0.11, 0.12, 0.13};

  double c[] = { 0.21, 0.22, 0.23,
                 0.00, 0.00, 1022,
                 1031, 1032, 1111 };
/*
  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&c[0], sizeof(c[0]), "c0");
  klee_make_symbolic(&c[1], sizeof(c[1]), "c1");
  klee_make_symbolic(&c[2], sizeof(c[2]), "c2");
  klee_make_symbolic(&c[3], sizeof(c[3]), "c3");
  klee_make_symbolic(&c[4], sizeof(c[4]), "c4");
  klee_make_symbolic(&c[5], sizeof(c[5]), "c5");
  klee_make_symbolic(&c[6], sizeof(c[6]), "c6");
  klee_make_symbolic(&c[7], sizeof(c[7]), "c7");
  klee_make_symbolic(&c[8], sizeof(c[8]), "c8");
*/
  gsl_vector_view X = gsl_vector_view_array(a, 3);
  gsl_matrix_view A = gsl_matrix_view_array(c, 3, 3);

  /* Compute C = A B */

  int status = gsl_blas_dtrmv(CblasUpper, CblasNoTrans, CblasNonUnit, &A.matrix, &X.vector);
  printf("%d\n", status);
  //printf ("[ %g, %g\n", c[0], c[1]);
  //printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
