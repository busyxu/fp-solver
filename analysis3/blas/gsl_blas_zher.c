// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0;
  double c0=0.21, c1=0.22, c2=0.23, c3=0.00, c4=0.00, c5=1022, c6=1031, c7=1032;
  double alpha=1;
  size_t Uplo = CblasUpper;

  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");

  double a[] = { a0, a1, a2, a3};
  double c[] = { c0, c1, c2, c3, c4, c5, c6, c7};

  gsl_vector_complex_view A = gsl_vector_complex_view_array(a, 2);
  gsl_matrix_complex_view C = gsl_matrix_complex_view_array(c, 2, 2);

  int status = gsl_blas_zher(Uplo, alpha, &A.vector, &C.matrix);
//  printf("%d\n", status);
//  printf ("[ %g, %g\n", c[0], c[1]);
//  printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
