#include <gsl/gsl_sf.h>
#include <klee/klee.h>

int main() {
  unsigned int a,b;
  klee_make_symbolic(&a, sizeof(a), "a");
  klee_make_symbolic(&b, sizeof(b), "b");

  gsl_sf_result result;
  int status = gsl_sf_choose_e(a,b,&result);
  return 0;
}



