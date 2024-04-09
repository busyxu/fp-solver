#include <gsl/gsl_sf.h>
#include <klee/klee.h>

int main() {
  int a;
  double b;
  klee_make_symbolic(&a, sizeof(a), "a");
  klee_make_symbolic(&b, sizeof(b), "b");

  gsl_sf_result result;
  int status = gsl_sf_hermite_func_fast_e(a,b,&result);
  return 0;
}


