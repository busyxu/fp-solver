/*=====add by yx =====*/

//#include <stdio.h>
#include <gsl/gsl_math.h>
//#include <klee/klee.h>

int main() {
  double a;
//  klee_make_symbolic(&a, sizeof(a), "a");
  
  double result = gsl_expm1(a);
  //printf("%lf\n",result);
  return 0;
}



