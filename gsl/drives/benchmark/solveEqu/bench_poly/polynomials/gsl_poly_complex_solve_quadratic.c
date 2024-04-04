

#include <stdio.h>
#include <gsl/gsl_poly.h>
#include <gsl/gsl_complex_math.h>
#include <klee/klee.h>

int main() {

  double x1,y1,x2,y2;

  klee_make_symbolic(&x1, sizeof(x1), "x1");
  klee_make_symbolic(&y1, sizeof(y1), "y1");
  klee_make_symbolic(&x2, sizeof(x2), "x2");
  klee_make_symbolic(&y2, sizeof(y2), "y2");

  gsl_complex z0 = gsl_complex_rect(x1, y1);
  gsl_complex z1 = gsl_complex_rect(x2, y2);

  double result = gsl_poly_complex_solve_quadratic(1.0, 1.0, 1.0, &z0, &z1);
  //printf("%lf\n",result);
  return 0;
}



