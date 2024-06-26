/*=====add by yx =====*/

#include <klee/klee.h>
#include <stdio.h>
#include <math.h>
#include <gsl/gsl_integration.h>

double f (double x, void * params) {
  double alpha = *(double *) params;
  double f = log(alpha*x) / sqrt(x);
  return f;
}

int main (void)
{
//  gsl_integration_workspace * w = gsl_integration_workspace_alloc (1000);

  double result, error;
  double expected = -4.0;
  double alpha = 1.0;
  double a=0,b=1,epsabs=100,epsrel=100;
  size_t neval=1000000;

  klee_make_symbolic(&a, sizeof(a), "a");
  klee_make_symbolic(&b, sizeof(b), "b");
  klee_make_symbolic(&epsabs, sizeof(epsabs), "epsabs");
  klee_make_symbolic(&epsrel, sizeof(epsrel), "epsrel");

  gsl_function F;
  F.function = &f;
  F.params = &alpha;

  gsl_integration_qng (&F, a, b, epsabs, epsrel, &result, &error, &neval);

//  printf ("result          = % .18f\n", result);
//  printf ("exact result    = % .18f\n", expected);
//  printf ("estimated error = % .18f\n", error);
//  printf ("actual error    = % .18f\n", result - expected);

//  gsl_integration_workspace_free (w);

  return 0;
}
