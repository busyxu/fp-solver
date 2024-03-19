// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0;
  double b0=1011, b1=1012;
  double c0=0.21, c1=0.22, c2=0.21, c3=0.22;
  double alpha=1;
  size_t Uplo = CblasUpper;

  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");

  double a[] = { a0, a1};
  double b[] = { b0, b1};
  double c[] = { c0, c1, c2, c3};
//  double alpha = 1.0;

  gsl_vector_view A = gsl_vector_view_array(a, 2);
  gsl_vector_view B = gsl_vector_view_array(b, 2);
  gsl_matrix_view C = gsl_matrix_view_array(c, 2, 2);

  int status = gsl_blas_dsyr2(Uplo, alpha, &A.vector, &B.vector, &C.matrix);
//  printf("%d\n", status);
//  for(int i=0; i<9; i++)
//    printf ("%g, ", c[i]);
//  printf ("\n");

  return 0;
}
