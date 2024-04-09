/*=====add by yx =====*/

#include <klee/klee.h>
#include <stdlib.h>
#include <gsl/gsl_math.h>
#include <gsl/gsl_monte.h>
#include <gsl/gsl_monte_plain.h>
#include <gsl/gsl_monte_miser.h>
#include <gsl/gsl_monte_vegas.h>

/* Computation of the integral,

      I = int (dx dy dz)/(2pi)^3  1/(1-cos(x)cos(y)cos(z))

   over (-pi,-pi,-pi) to (+pi, +pi, +pi).  The exact answer
   is Gamma(1/4)^4/(4 pi^3).  This example is taken from
   C.Itzykson, J.M.Drouffe, "Statistical Field Theory -
   Volume 1", Section 1.1, p21, which cites the original
   paper M.L.Glasser, I.J.Zucker, Proc.Natl.Acad.Sci.USA 74
   1800 (1977) */

/* For simplicity we compute the integral over the region
   (0,0,0) -> (pi,pi,pi) and multiply by 8 */

double exact = 1.3932039296856768591842462603255;

double
g (double *k, size_t dim, void *params)
{
  (void)(dim); /* avoid unused parameter warnings */
  (void)(params);
  double A = 1.0 / (M_PI * M_PI * M_PI);
  return A / (1.0 - cos (k[0]) * cos (k[1]) * cos (k[2]));
}

void
display_results (char *title, double result, double error)
{
  printf ("%s ==================\n", title);
  printf ("result = % .6f\n", result);
  printf ("sigma  = % .6f\n", error);
  printf ("exact  = % .6f\n", exact);
  printf ("error  = % .6f = %.2g sigma\n", result - exact,
          fabs (result - exact) / error);
}

int
main (void)
{
  double res, err;
  double l0=0,l1=0,l2=0;
  double u0=1,u1=1,u2=1;

  klee_make_symbolic(&l0, sizeof(l0), "l0");
  klee_make_symbolic(&l1, sizeof(l1), "l1");
  klee_make_symbolic(&l2, sizeof(l2), "l2");
  klee_make_symbolic(&u0, sizeof(u0), "u0");
  klee_make_symbolic(&u1, sizeof(u1), "u1");
  klee_make_symbolic(&u2, sizeof(u2), "u2");

  double xl[3] = { l0, l1, l2 };
  double xu[3] = { u0, u1, u2 };

  const gsl_rng_type *T;
  gsl_rng *r;

  gsl_monte_function G = { &g, 3, 0 };

  size_t calls = 500000;

  gsl_rng_env_setup ();

  T = gsl_rng_default;
  r = gsl_rng_alloc (T);

  {
    gsl_monte_miser_state *s = gsl_monte_miser_alloc (3);
    gsl_monte_miser_integrate (&G, xl, xu, 3, calls, r, s,
                               &res, &err);
    gsl_monte_miser_free (s);

    display_results ("miser", res, err);
  }

  gsl_rng_free (r);

  return 0;
}