// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11;
  double alpha=1;
  size_t Side = CblasLeft;
  size_t Uplo = CblasUpper;
  size_t TransA = CblasNoTrans;
  size_t Diag = CblasNonUnit;
  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
  klee_make_symbolic(&Side, sizeof(Side), "Side");
  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");
  klee_make_symbolic(&TransA, sizeof(TransA), "TransA");
  klee_make_symbolic(&Diag, sizeof(Diag), "Diag");

  double a[] = { a0, a1, a2, a3};
  double b[] = { b0, b1, b2, b3};

  gsl_matrix_view A = gsl_matrix_view_array(a, 2, 2);
  gsl_matrix_view B = gsl_matrix_view_array(b, 2, 2);

  int status = gsl_blas_dtrmm(Side, Uplo, TransA, Diag, alpha, &A.matrix, &B.matrix);
//  printf("%d\n", status);
//  printf ("[ %g, %g\n", b[0], b[1]);
//  printf ("  %g, %g ]\n", b[2], b[3]);

  return 0;
}
