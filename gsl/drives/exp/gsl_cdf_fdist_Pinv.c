//
// Created by liukunlin on 2021/8/31.
//
#include "klee/klee.h"
#include "gsl/gsl_cdf.h"
int main()
{
    double x,nu1,nu2;
    klee_make_symbolic(&x, sizeof(x),"x");
    klee_make_symbolic(&nu1, sizeof(nu1),"nu1");
    klee_make_symbolic(&nu2, sizeof(nu2),"nu2");
    gsl_cdf_fdist_Pinv(x, nu1, nu2);

}