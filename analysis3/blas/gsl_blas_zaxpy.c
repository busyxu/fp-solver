// ======== add by yx ========
#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{
  double a0=1, a1=0, a2=1, a3=0;
  double b0=1011, b1=1012, b2=1021, b3=0.11;
  double alpha0=1,alpha1=0;
  klee_make_symbolic(&alpha0, sizeof(alpha0), "alpha0");
  klee_make_symbolic(&alpha1, sizeof(alpha1), "alpha1");

  double a[] = { a0, a1, a2, a3};
  double b[] = { b0, b1, b2, b3};

  gsl_complex alpha = {{alpha0, alpha1}};

  gsl_vector_complex_view A = gsl_vector_complex_view_array(a, 2);
  gsl_vector_complex_view B = gsl_vector_complex_view_array(b, 2);

  int status = gsl_blas_zaxpy(alpha, &A.vector, &B.vector);
//  printf("%d\n", status);
//  for(int i=0; i<8; i++)
//    printf ("%g, ", b[i]);
//  printf ("\n");
  
  return 0;
}
