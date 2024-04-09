#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  double a[] = { 0.11, 0.12, 0.13, 0.25, 0.11, 0.12, 0.13, 0.25};

  double b[] = { 0.21, 0.22, 0.23, 1022, 0.11, 0.12, 0.13, 0.25};
/*
  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&a[3], sizeof(a[3]), "a3");
  klee_make_symbolic(&a[4], sizeof(a[4]), "a4");
  klee_make_symbolic(&a[5], sizeof(a[5]), "a5");
  klee_make_symbolic(&a[6], sizeof(a[6]), "a6");
  klee_make_symbolic(&a[7], sizeof(a[7]), "a7");

  klee_make_symbolic(&b[0], sizeof(b[0]), "b0");
  klee_make_symbolic(&b[1], sizeof(b[1]), "b1");
  klee_make_symbolic(&b[2], sizeof(b[2]), "b2");
  klee_make_symbolic(&b[3], sizeof(b[3]), "b3");
  klee_make_symbolic(&b[4], sizeof(b[4]), "b4");
  klee_make_symbolic(&b[5], sizeof(b[5]), "b5");
  klee_make_symbolic(&b[6], sizeof(b[6]), "b6");
  klee_make_symbolic(&b[7], sizeof(b[7]), "b7");
*/
  gsl_matrix_complex_view A = gsl_matrix_complex_view_array(a, 2, 2);
  gsl_matrix_complex_view B = gsl_matrix_complex_view_array(b, 2, 2);

  /* Compute C = A B */

  int status = gsl_blas_zherk(CblasUpper, CblasNoTrans, 1.0, &A.matrix, 1.0, &B.matrix);
  printf("%d\n", status);

  return 0;
}