#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  double a[] = { 0.11, 0.12, 0.13, 0.11};

  double c[] = { 0.21, 0.22, 0.23, 0.00,
                 1022, 1031, 1032, 1111 };

  double alpha = 1.0;
/*
  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&a[3], sizeof(a[3]), "a3");
  klee_make_symbolic(&c[0], sizeof(c[0]), "c0");
  klee_make_symbolic(&c[1], sizeof(c[1]), "c1");
  klee_make_symbolic(&c[2], sizeof(c[2]), "c2");
  klee_make_symbolic(&c[3], sizeof(c[3]), "c3");
  klee_make_symbolic(&c[4], sizeof(c[4]), "c4");
  klee_make_symbolic(&c[5], sizeof(c[5]), "c5");
  klee_make_symbolic(&c[6], sizeof(c[6]), "c6");
  klee_make_symbolic(&c[7], sizeof(c[7]), "c7");
*/
  gsl_vector_complex_view A = gsl_vector_complex_view_array(a, 2);
  gsl_matrix_complex_view C = gsl_matrix_complex_view_array(c, 2, 2);

  /* Compute C = A B */

  int status = gsl_blas_zher(CblasUpper, alpha, &A.vector, &C.matrix);
  printf("%d\n", status);
  //printf ("[ %g, %g\n", c[0], c[1]);
  //printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
