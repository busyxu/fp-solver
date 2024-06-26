// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
//#include <klee/klee.h>

int main (void)
{

  double a0=1, a1=0, a2=1, a3=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11;
  double c0=0.21, c1=0.22, c2=0.23, c3=0.00;
  double alpha=1,beta=1;
  size_t Trans = CblasLeft;
  size_t Uplo = CblasUpper;
//  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
//  klee_make_symbolic(&beta, sizeof(beta), "beta");
//  klee_make_symbolic(&Trans, sizeof(Trans), "Trans");
//  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");

//  klee_make_symbolic(&a0, sizeof(a0), "a0");
//  klee_make_symbolic(&a1, sizeof(a1), "a1");
//  klee_make_symbolic(&a2, sizeof(a2), "a2");
//  klee_make_symbolic(&a3, sizeof(a3), "a3");
//  klee_make_symbolic(&b0, sizeof(b0), "b0");
//  klee_make_symbolic(&b1, sizeof(b1), "b1");
//  klee_make_symbolic(&b2, sizeof(b2), "b2");
//  klee_make_symbolic(&b3, sizeof(b3), "b3");
//  klee_make_symbolic(&c0, sizeof(c0), "c0");
//  klee_make_symbolic(&c1, sizeof(c1), "c1");
//  klee_make_symbolic(&c2, sizeof(c2), "c2");
//  klee_make_symbolic(&c3, sizeof(c3), "c3");

  double a[] = { a0, a1, a2, a3};
  double b[] = { b0, b1, b2, b3};
  double c[] = { c0, c1, c2, c3};

  gsl_matrix_view A = gsl_matrix_view_array(a, 2, 2);
  gsl_matrix_view B = gsl_matrix_view_array(b, 2, 2);
  gsl_matrix_view C = gsl_matrix_view_array(c, 2, 2);

  int status = gsl_blas_dsyr2k(Uplo, Trans, alpha, &A.matrix, &B.matrix, beta, &C.matrix);
  printf("%d\n", status);
  printf ("[ %g, %g\n", b[0], b[1]);
  printf ("  %g, %g ]\n", b[2], b[3]);

  return 0;
}
