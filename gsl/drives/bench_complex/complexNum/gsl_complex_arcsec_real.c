

//#include <stdio.h>
#include <gsl/gsl_complex_math.h>
#include <klee/klee.h>

int main() {
  double x;
  klee_make_symbolic(&x1, sizeof(x), "x");

  gsl_complex result = gsl_complex_arcsec_real(x);
  //printf("%lf\n",result);
  return 0;
}



