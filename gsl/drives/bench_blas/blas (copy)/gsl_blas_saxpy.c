#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  float a[] = { 0.11, 0.12, 0.13, 0.21, 0.22, 0.23 };

  float b[] = { 1011, 1012,
                 1021, 1022,
                 1031, 1032 };

  float alpha=1.0;

  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&a[3], sizeof(a[3]), "a3");
  klee_make_symbolic(&a[4], sizeof(a[4]), "a4");
  klee_make_symbolic(&a[5], sizeof(a[5]), "a5");
  klee_make_symbolic(&b[0], sizeof(b[0]), "b0");
  klee_make_symbolic(&b[1], sizeof(b[1]), "b1");
  klee_make_symbolic(&b[2], sizeof(b[2]), "b2");
  klee_make_symbolic(&b[3], sizeof(b[3]), "b3");
  klee_make_symbolic(&b[4], sizeof(b[4]), "b4");
  klee_make_symbolic(&b[5], sizeof(b[5]), "b5");
  klee_make_symbolic(&alpha, sizeof(alpha), "alpha");

  gsl_vector_float_view A = gsl_vector_float_view_array(a, 6);
  gsl_vector_float_view B = gsl_vector_float_view_array(b, 6);

  int status = gsl_blas_saxpy(alpha, &A.vector, &B.vector);
  printf("%d\n", status);
  //printf("%g\n", dotu);
  //gsl_vector_float_free(&A);
  //gsl_vector_float_free(&B);
  //gsl_vector_float_free(dotu);
  
  return 0;
}