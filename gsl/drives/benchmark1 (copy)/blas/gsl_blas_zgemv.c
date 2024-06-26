// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
//#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11;
  double c0=0.21, c1=0.22, c2=0.23, c3=0.00, c4=0.00, c5=1022, c6=1031, c7=1032;
  double alpha0=1, alpha1=0, beta0=1, beta1=0;
  size_t TransA = CblasNoTrans;
//  klee_make_symbolic(&alpha0, sizeof(alpha0), "alpha0");
//  klee_make_symbolic(&alpha1, sizeof(alpha1), "alpha1");
//  klee_make_symbolic(&beta0, sizeof(beta0), "beta0");
//  klee_make_symbolic(&beta1, sizeof(beta1), "beta1");
//  klee_make_symbolic(&TransA, sizeof(TransA), "TransA");
//
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
//  klee_make_symbolic(&c4, sizeof(c4), "c4");
//  klee_make_symbolic(&c5, sizeof(c5), "c5");
//  klee_make_symbolic(&c6, sizeof(c6), "c6");
//  klee_make_symbolic(&c7, sizeof(c7), "c7");

  double a[] = { a0, a1, a2, a3};
  double b[] = { b0, b1, b2, b3};
  double c[] = { c0, c1, c2, c3, c4, c5, c6, c7};
  gsl_complex alpha = {{alpha0,alpha1}};
  gsl_complex beta = {{beta0,beta1}};

  gsl_vector_complex_view B = gsl_vector_complex_view_array(b, 2);
  gsl_vector_complex_view C = gsl_vector_complex_view_array(c, 2);
  gsl_matrix_complex_view A = gsl_matrix_complex_view_array(a, 2, 2);

  int status = gsl_blas_zgemv(TransA, alpha, &A.matrix, &B.vector, beta, &C.vector);
  printf("%d\n", status);
  for(int i=0; i<4; i++)
    printf ("%g, ", c[i]);
  printf ("\n");

  return 0;
}
