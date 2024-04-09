/*=====add by yx =====*/
#include <stdio.h>
#include <gsl/gsl_blas.h>
//#include <gsl/gsl_complex_math.h>
#include <klee/klee.h>

int main (void)
{
  
  //double c1,c2,c3  

  double a[] = { 0.11, 0.12, 0.13, 0.21, 1, 2, 3, 4};

  double b[] = { 1011, 1012, 1021, 1022, 5, 6, 7, 8};

  double c[] = { 1.00, 1.00, 1.00, 1.00, 1, 1, 1, 1};

//  gsl_complex alpha = gsl_complex_rect(1.0,1.0);
//  gsl_complex beta = gsl_complex_rect(1.0,1.0);
  gsl_complex alpha = {{1.0,0.0}};
  gsl_complex beta = {{1.0,0.0}};
  /*
  klee_make_symbolic(&a[0], sizeof(a[0]), "a0");
  klee_make_symbolic(&a[1], sizeof(a[1]), "a1");
  klee_make_symbolic(&a[2], sizeof(a[2]), "a2");
  klee_make_symbolic(&a[3], sizeof(a[3]), "a3");
  klee_make_symbolic(&a[4], sizeof(a[4]), "a4");
  klee_make_symbolic(&a[5], sizeof(a[5]), "a5");
  klee_make_symbolic(&a[6], sizeof(a[6]), "a6");
  klee_make_symbolic(&a[7], sizeof(a[7]), "a7");
  klee_make_symbolic(&b[0], sizeof(b[0]), "b0");
  klee_make_symbolic(&b[1], sizeof(b[1]), "b1");
  klee_make_symbolic(&b[2], sizeof(b[2]), "b2");
  klee_make_symbolic(&b[3], sizeof(b[3]), "b3");
  klee_make_symbolic(&b[4], sizeof(b[4]), "b4");
  klee_make_symbolic(&b[5], sizeof(b[5]), "b5");
  klee_make_symbolic(&b[6], sizeof(b[6]), "b6");
  klee_make_symbolic(&b[7], sizeof(b[7]), "b7");
  klee_make_symbolic(&c[0], sizeof(c[0]), "c0");
  klee_make_symbolic(&c[1], sizeof(c[1]), "c1");
  klee_make_symbolic(&c[2], sizeof(c[2]), "c2");
  klee_make_symbolic(&c[3], sizeof(c[3]), "c3");
  klee_make_symbolic(&c[4], sizeof(c[4]), "c4");
  klee_make_symbolic(&c[5], sizeof(c[5]), "c5");
  klee_make_symbolic(&c[6], sizeof(c[6]), "c6");
  klee_make_symbolic(&c[7], sizeof(c[7]), "c7");
*/
  gsl_matrix_complex_view A = gsl_matrix_complex_view_array(a, 2, 2);
  gsl_matrix_complex_view B = gsl_matrix_complex_view_array(b, 2, 2);
  gsl_matrix_complex_view C = gsl_matrix_complex_view_array(c, 2, 2);

  /* Compute C = A B */

  gsl_blas_zsymm (CblasLeft, CblasUpper,
                  alpha, &A.matrix, &B.matrix,
                  beta, &C.matrix);

  for(int i=0; i<8; i++)
    printf ("%g, ", c[i]);
  printf ("\n");

  return 0;
}