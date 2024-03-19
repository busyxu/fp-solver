// ======== add by yx ========

#include <stdio.h>
#include <gsl/gsl_blas.h>
//#include <gsl/gsl_complex_math.h>
#include <klee/klee.h>

int main (void)
{
  float a0=1, a1=0, a2=1, a3=0, a4=1, a5=0, a6=1, a7=0;
  float b0=1011, b1=1012, b2=1021, b3=0.11, b4=1011, b5=1012, b6=1021, b7=0.11;
  float c0=0.21, c1=0.22, c2=0.23, c3=0.00, c4=0.00, c5=1022, c6=1031, c7=1032;
  float alpha0=1, alpha1=1, beta0=1, beta1=1;
  size_t TransA = CblasNoTrans;
  size_t TransB = CblasNoTrans;
  klee_make_symbolic(&alpha0, sizeof(alpha0), "alpha0");
  klee_make_symbolic(&alpha1, sizeof(alpha1), "alpha1");
  klee_make_symbolic(&beta0, sizeof(beta0), "beta0");
  klee_make_symbolic(&beta1, sizeof(beta1), "beta1");
  klee_make_symbolic(&TransA, sizeof(TransA), "TransA");
  klee_make_symbolic(&TransB, sizeof(TransB), "TransB");
  gsl_complex_float alpha = {{alpha0, alpha1}};
  gsl_complex_float beta = {{beta0, beta1}};

  float a[] = { a0, a1, a2, a3, a4, a5, a6, a7};
  float b[] = { b0, b1, b2, b3, b4, b5, b6, b7};
  float c[] = { c0, c1, c2, c3, c4, c5, c6, c7};

  gsl_matrix_complex_float_view A = gsl_matrix_complex_float_view_array(a, 2, 2);
  gsl_matrix_complex_float_view B = gsl_matrix_complex_float_view_array(b, 2, 2);
  gsl_matrix_complex_float_view C = gsl_matrix_complex_float_view_array(c, 2, 2);

  gsl_blas_cgemm (TransA, TransB,
                  alpha, &A.matrix, &B.matrix,
                  beta, &C.matrix);

//  printf ("[ %g, %g\n", c[0], c[1]);
//  printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
