// ======== add by yx ========

#include <stdio.h>
#include <gsl/gsl_blas.h>
//#include <gsl/gsl_complex_math.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11;
  double c0=0.21, c1=0.22, c2=0.23, c3=0.00;
  double alpha=1, beta=1;
  size_t Side = CblasLeft;
  size_t Uplo = CblasUpper;
  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
  klee_make_symbolic(&beta, sizeof(beta), "beta");
  klee_make_symbolic(&Side, sizeof(Side), "Side");
  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");

  double a[] = { a0, a1, a2, a3};
  double b[] = { b0, b1, b2, b3};
  double c[] = { c0, c1, c2, c3};
//  double alpha = 1.0;
//  double beta = 1.0;

  gsl_matrix_view A = gsl_matrix_view_array(a, 2, 2);
  gsl_matrix_view B = gsl_matrix_view_array(b, 2, 2);
  gsl_matrix_view C = gsl_matrix_view_array(c, 2, 2);

  gsl_blas_dsymm (Side, Uplo,
                  alpha, &A.matrix, &B.matrix,
                  beta, &C.matrix);

//  printf ("[ %g, %g\n", c[0], c[1]);
//  printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
