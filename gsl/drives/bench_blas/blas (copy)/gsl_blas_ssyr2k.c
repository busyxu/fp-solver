#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  float a[] = { 0.11, 0.12, 0.13, 0.25};

  float b[] = { 0.21, 0.22, 0.23, 1022};
  float c[] = { 0.21, 0.22, 0.23, 1022};
/*
  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&a[3], sizeof(a[3]), "a3");
  klee_make_symbolic(&b[0], sizeof(b[0]), "b0");
  klee_make_symbolic(&b[1], sizeof(b[1]), "b1");
  klee_make_symbolic(&b[2], sizeof(b[2]), "b2");
  klee_make_symbolic(&b[3], sizeof(b[3]), "b3");
  klee_make_symbolic(&c[0], sizeof(c[0]), "c0");
  klee_make_symbolic(&c[1], sizeof(c[1]), "c1");
  klee_make_symbolic(&c[2], sizeof(c[2]), "c2");
  klee_make_symbolic(&c[3], sizeof(c[3]), "c3");
*/
  gsl_matrix_float_view A = gsl_matrix_float_view_array(a, 2, 2);
  gsl_matrix_float_view B = gsl_matrix_float_view_array(b, 2, 2);
  gsl_matrix_float_view C = gsl_matrix_float_view_array(c, 2, 2);

  /* Compute C = A B */

  int status = gsl_blas_ssyr2k(CblasUpper, CblasNoTrans, 1.0, &A.matrix, &B.matrix, 1.0, &C.matrix);
  printf("%d\n", status);
  printf ("[ %g, %g\n", b[0], b[1]);
  printf ("  %g, %g ]\n", b[2], b[3]);

  return 0;
}
