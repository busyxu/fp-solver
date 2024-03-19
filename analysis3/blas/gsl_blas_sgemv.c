// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  float a0=1, a1=0;
  float b0=1011, b1=1012;
  float c0=0.21, c1=0.22, c2=0.23, c3=0.00;
  float alpha=1, beta=1;
  size_t TransA = CblasNoTrans;
  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");
  klee_make_symbolic(&beta, sizeof(beta), "beta");
  klee_make_symbolic(&TransA, sizeof(TransA), "TransA");

  float a[] = { a0, a1};
  float b[] = { b0, b1};
  float c[] = { c0, c1, c2, c3};

  gsl_vector_float_view A = gsl_vector_float_view_array(a, 2);
  gsl_vector_float_view B = gsl_vector_float_view_array(b, 2);
  gsl_matrix_float_view C = gsl_matrix_float_view_array(c, 2, 2);

  int status = gsl_blas_sgemv(TransA, alpha, &C.matrix, &A.vector, beta, &B.vector);
//  printf("%d\n", status);
//  printf ("[ %g, %g\n", c[0], c[1]);
//  printf ("  %g, %g ]\n", c[2], c[3]);

  return 0;
}
