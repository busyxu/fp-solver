// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  float a0=1, a1=0, a2=1, a3=0;
  float c0=0.21, c1=0.22, c2=0.23, c3=0.00, c4=0.00, c5=1022, c6=1031, c7=1032;
  size_t Uplo = CblasUpper;
  size_t Trans = CblasNoTrans;
  size_t Diag = CblasNonUnit;

  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");
  klee_make_symbolic(&Trans, sizeof(Trans), "Trans");
  klee_make_symbolic(&Diag, sizeof(Diag), "Diag");

  float a[] = { a0, a1, a2, a3};
  float c[] = { c0, c1, c2, c3, c4, c5, c6, c7};

  gsl_vector_complex_float_view X = gsl_vector_complex_float_view_array(a, 2);
  gsl_matrix_complex_float_view A = gsl_matrix_complex_float_view_array(c, 2, 2);

  int status = gsl_blas_ctrsv(Uplo, Trans, Diag, &A.matrix, &X.vector);
//  printf("%d\n", status);
//  printf ("[ %g, %g\n", c[0], c[1]);
//  printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
