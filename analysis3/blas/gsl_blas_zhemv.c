// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11;
  double c0=0.21, c1=0.22, c2=0.23, c3=0.00, c4=0.00, c5=1022, c6=1031, c7=1032;
  double alpha0=1, alpha1=1, beta0=1, beta1=1;
  size_t Uplo = CblasUpper;

  klee_make_symbolic(&alpha0, sizeof(alpha0), "alpha0");
  klee_make_symbolic(&alpha1, sizeof(alpha1), "alpha1");
  klee_make_symbolic(&beta0, sizeof(beta0), "beta0");
  klee_make_symbolic(&beta1, sizeof(beta1), "beta1");
  klee_make_symbolic(&Uplo, sizeof(Uplo), "Uplo");
  gsl_complex alpha = {{alpha0, alpha1}};
  gsl_complex beta = {{beta0, beta1}};

  double a[] = { a0, a1, a2, a3};
  double b[] = { b0, b1, b2, b3};
  double c[] = { c0, c1, c2, c3, c4, c5, c6, c7};
//  gsl_complex alpha = {{1.0,1.0}};
//  gsl_complex beta = {{1.0,1.0}};

  gsl_vector_complex_view B = gsl_vector_complex_view_array(b, 2);
  gsl_vector_complex_view C = gsl_vector_complex_view_array(c, 2);
  gsl_matrix_complex_view A = gsl_matrix_complex_view_array(a, 2, 2);

  

  int status = gsl_blas_zhemv(Uplo, alpha, &A.matrix, &B.vector, beta, &C.vector);
//  printf("%d\n", status);
//  for(int i=0; i<4; i++)
//    printf ("%g, ", c[i]);
//  printf ("\n");

  return 0;
}
