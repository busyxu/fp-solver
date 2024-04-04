/*=====add by yx =====*/

#include <klee/klee.h>
#include <stdio.h>
#include <gsl/gsl_errno.h>
#include <gsl/gsl_math.h>
#include <gsl/gsl_roots.h>

struct quadratic_params
{
    double a, b, c;
};

double quadratic (double x, void *params);
double quadratic_deriv (double x, void *params);
void quadratic_fdf (double x, void *params,
                    double *y, double *dy);

double
quadratic (double x, void *params)
{
  struct quadratic_params *p
          = (struct quadratic_params *) params;

  double a = p->a;
  double b = p->b;
  double c = p->c;

  return (a * x + b) * x + c;
}

double
quadratic_deriv (double x, void *params)
{
  struct quadratic_params *p
          = (struct quadratic_params *) params;

  double a = p->a;
  double b = p->b;

  return 2.0 * a * x + b;
}

void
quadratic_fdf (double x, void *params,
               double *y, double *dy)
{
  struct quadratic_params *p
          = (struct quadratic_params *) params;

  double a = p->a;
  double b = p->b;
  double c = p->c;

  *y = (a * x + b) * x + c;
  *dy = 2.0 * a * x + b;
}

int
main (void)
{
  int status;
  int iter = 0, max_iter = 3;
  const gsl_root_fdfsolver_type *T;
  gsl_root_fdfsolver *s;
  double r_expected = sqrt (5.0);
  double x0=0, x=5, epsabs=0, epsrel=1e-3;
  gsl_function_fdf FDF;
  struct quadratic_params params = {1.0, 0.0, -5.0};

  klee_make_symbolic(&x0, sizeof(x0), "x0");
  klee_make_symbolic(&x, sizeof(x), "x");
  klee_make_symbolic(&epsabs, sizeof(epsabs), "epsabs");
  klee_make_symbolic(&epsrel, sizeof(epsrel), "epsrel");

  FDF.f = &quadratic;
  FDF.df = &quadratic_deriv;
  FDF.fdf = &quadratic_fdf;
  FDF.params = &params;

  T = gsl_root_fdfsolver_newton;
  s = gsl_root_fdfsolver_alloc (T);
  gsl_root_fdfsolver_set (s, &FDF, x);

  printf ("using %s method\n",
          gsl_root_fdfsolver_name (s));

  printf ("%-5s %10s %10s %10s\n",
          "iter", "root", "err", "err(est)");
  do
  {
    iter++;
    status = gsl_root_fdfsolver_iterate (s);
    x0 = x;
    x = gsl_root_fdfsolver_root (s);
    status = gsl_root_test_delta (x, x0, epsabs, epsrel);

    if (status == GSL_SUCCESS)
      printf ("Converged:\n");

    printf ("%5d %10.7f %+10.7f %10.7f\n",
            iter, x, x - r_expected, x - x0);
  }
  while (status == GSL_CONTINUE && iter < max_iter);

  gsl_root_fdfsolver_free (s);
  return status;
}