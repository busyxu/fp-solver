// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0, a4=1, a5=0, a6=1, a7=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11, b4=1011, b5=1012, b6=1021, b7=0.11;
  double alpha=1, beta=1;
  size_t Uplo = CblasUpper;
  size_t Trans = CblasNoTrans;

  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
  klee_make_symbolic(&beta, sizeof(beta), "beta");
  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");
  klee_make_symbolic(&Trans, sizeof(Trans), "Trans");

  double a[] = { a0, a1, a2, a3, a4, a5, a6, a7};
  double b[] = { b0, b1, b2, b3, b4, b5, b6, b7};

  gsl_matrix_complex_view A = gsl_matrix_complex_view_array(a, 2, 2);
  gsl_matrix_complex_view B = gsl_matrix_complex_view_array(b, 2, 2);

  int status = gsl_blas_zherk(Uplo, Trans, alpha, &A.matrix, beta, &B.matrix);
//  printf("%d\n", status);

  return 0;
}
