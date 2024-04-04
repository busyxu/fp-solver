#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  float a[] = { 0.11, 0.12, 0.13, 0.21, 0.22, 0.23, 1, 1};

  gsl_complex_float alpha = {{2.0, 0.0}};
/*
  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&a[3], sizeof(a[3]), "a3");
  klee_make_symbolic(&a[4], sizeof(a[4]), "a4");
  klee_make_symbolic(&a[5], sizeof(a[5]), "a5");
  klee_make_symbolic(&a[6], sizeof(a[6]), "a6");
  klee_make_symbolic(&a[7], sizeof(a[7]), "a7");
*/
  gsl_vector_complex_float_view A = gsl_vector_complex_float_view_array(a, 4);

  gsl_blas_cscal(alpha, &A.vector);

  for(int i=0; i<8; i++)
    printf ("%g, ", a[i]);
  printf ("\n");
  
  return 0;
}
