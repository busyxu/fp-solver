#include <stdio.h>
#include <gsl/gsl_blas.h>
#include <klee/klee.h>

int main (void)
{

  float a[] = {0.11, 0.12, 0.13};
  float b[] = {0.21, 0.22, 0.23};
  float c[] = {1011, 1012, 1021};
  float s[] = {1022, 1031, 1032};

  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&b[0], sizeof(b[0]), "b0");
  klee_make_symbolic(&b[1], sizeof(b[1]), "b1");
  klee_make_symbolic(&b[2], sizeof(b[2]), "b2");
  klee_make_symbolic(&c[0], sizeof(c[0]), "c0");
  klee_make_symbolic(&c[1], sizeof(c[1]), "c1");
  klee_make_symbolic(&c[2], sizeof(c[2]), "c2");
  klee_make_symbolic(&s[0], sizeof(s[0]), "s0");
  klee_make_symbolic(&s[1], sizeof(s[1]), "s1");
  klee_make_symbolic(&s[2], sizeof(s[2]), "s2");

  int status = gsl_blas_srotg(a, b, c, s);
  printf("%d\n", status);
  //printf("%g\n", dotu);
  //gsl_vector_float_free(&A);
  //gsl_vector_float_free(&B);
  //gsl_vector_float_free(dotu);
  
  return 0;
}
