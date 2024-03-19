#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0;
  double b0=1011, b1=1012;
  double c0=0.21, c1=0.22, c2=0.21, c3=0.22;
  double alpha=1, beta=1;
  size_t Uplo = CblasUpper;
  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
  klee_make_symbolic(&beta, sizeof(beta), "beta");
  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");

  double a[] = { a0, a1};
  double b[] = { b0, b1};
  double c[] = { c0, c1, c2, c3};

  gsl_vector_view A = gsl_vector_view_array(a, 2);
  gsl_vector_view B = gsl_vector_view_array(b, 2);
  gsl_matrix_view C = gsl_matrix_view_array(c, 2, 2);

  int status = gsl_blas_dsymv(Uplo, alpha, &C.matrix, &A.vector, beta, &B.vector);
//  printf("%d\n", status);
//  printf ("[ %g, %g\n", c[0], c[1]);
//  printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
