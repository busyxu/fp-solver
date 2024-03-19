// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11, b4=1011, b5=1012, b6=1021, b7=0.11;
  size_t Uplo = CblasUpper;
  size_t Trans = CblasNoTrans;
  size_t Diag = CblasNonUnit;

  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");
  klee_make_symbolic(&Trans, sizeof(Trans), "Trans");
  klee_make_symbolic(&Diag, sizeof(Diag), "Diag");

  double a[] = { a0, a1, a2, a3};
  double b[] = { b0, b1, b2, b3, b4, b5, b6, b7};

  gsl_vector_complex_view X = gsl_vector_complex_view_array(a, 2);
  gsl_matrix_complex_view A = gsl_matrix_complex_view_array(b, 2, 2);

  int status = gsl_blas_ztrsv(Uplo, Trans, Diag, &A.matrix, &X.vector);
//  printf("%d\n", status);
//  printf ("[ %g, %g\n", c[0], c[1]);
//  printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
