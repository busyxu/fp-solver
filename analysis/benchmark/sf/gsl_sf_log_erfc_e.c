#include <gsl/gsl_sf.h>
#include <klee/klee.h>

int main() {
  double a;
  klee_make_symbolic(&a, sizeof(a), "a");

  gsl_sf_result result;
  int status = gsl_sf_log_erfc_e(a,&result);
  return 0;
}


