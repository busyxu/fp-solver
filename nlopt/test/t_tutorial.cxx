#include <iostream>
#include <vector>
#include <string>
#include <cmath>
#include <iomanip>
#include <nlopt.hpp>
//#include <nlopt.h>
//#define cnt 0

int a = 0;
double myfunc(unsigned n, const double *x, double *grad, void *data)
{
//  dim = 2;
  a++;
//  printf("double:\n");
//  std::cout<<x[0]<<" "<<x[1]<<" "<<fabs(x[0]-1)+fabs(x[1])<<"\n";

  return fabs(x[0]-1)+fabs(x[1]);
}


int main() {

//  nlopt::opt opt("LD_MMA", 2);
  nlopt_opt opt;
  opt = nlopt_create(NLOPT_GN_BYTEEA,16);

//  std::vector<double> lb(2);
//  lb[0] = -HUGE_VAL; lb[1] = 0;//lower bounds
  nlopt_set_lower_bounds1(opt, 0);
  nlopt_set_upper_bounds1(opt, 255);
  nlopt_set_min_objective(opt, myfunc, NULL);
//  std::vector<double> step_size_arr(2, 0.5);
//  nlopt_set_initial_step(opt, step_size_arr.data());
  nlopt_set_stopval(opt, 0);
  nlopt_set_xtol_rel(opt, 1e-10);
  nlopt_set_maxeval(opt, 500000);
  nlopt_set_population(opt, 200);

  double x[16] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
//  x[0] = 1.234; x[1] = 5.678;//initial value
  double minf=1.0;

  try{
    nlopt_optimize(opt, x, &minf);
    printf("solution:\n");
    for(int j=0; j<16; j++){
      printf("%d ",(int) x[j]);
    }
    printf("\n");
    int nvar = 16/8;
//    double *dval = malloc(sizeof(double) * nvar);
    double *dval = new double[nvar];
    for (int i = 0; i < nvar; i++) {
      uint8_t bytes[8];
      for (int j = 0; j < 8; j++) {
        bytes[j] = x[i*8+j];
      }
      double d;
      memcpy(&d, bytes, sizeof(double));
      dval[i] = d;
    }
    for(int i=0; i<nvar; i++){
      printf("%lf ",dval[i]);
    }
    printf("%lf\n",minf);
//    std::cout << x[0]<<" "<<x[1]<<" "<<minf<<"\n";
    std::cout<<a<<"\n";
    nlopt_destroy(opt);
    return 1;
  }
  catch(std::exception &e) {
    std::cerr << "nlopt failed: " << e.what() << std::endl;
    return EXIT_FAILURE;
  }
}
