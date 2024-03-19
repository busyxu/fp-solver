/* goSAT: automatically generated file */

#include "gofuncs.h"
#include <math.h>

#include <stdint.h>

double fp64_dis(const double a, const double b) {
    if (a == b || isnan(a) || isnan(b)) {
        return 0;
    }
    const double scale = pow(2, 54);
    uint64_t a_uint = *(const uint64_t *)(&a);
    uint64_t b_uint = *(const uint64_t *)(&b);
    if ((a_uint & 0x8000000000000000) != (b_uint & 0x8000000000000000)) {
        // signs are not equal return sum
        return ((double)
        ((a_uint & 0x7FFFFFFFFFFFFFFF) + (b_uint & 0x7FFFFFFFFFFFFFFF)))/scale;
    }
    b_uint &= 0x7FFFFFFFFFFFFFFF;
    a_uint &= 0x7FFFFFFFFFFFFFFF;
    if (a_uint < b_uint) {
        return ((double)(b_uint - a_uint))/scale;
    }
    return ((double)(a_uint - b_uint))/scale;
}

double (unsigned n, const double * x, double * grad, void * data){ 
const double expr_2798091491 = x[0] ;
const double expr_954062213 = 0;
const double expr_1586913185 = (expr_2798091491 >= expr_954062213)? 0: fp64_dis(expr_2798091491,expr_954062213);
const double expr_3157305753n = (expr_2798091491 != expr_954062213)? 0: 1 ;
const double expr_1168251917 = expr_3157305753n;
const double expr_783810685 = x[1] ;
const double expr_2730566147n = (expr_783810685 != expr_954062213)? 0: 1 ;
const double expr_1542123215 = expr_2730566147n;
const double expr_2831327593 = 1.000000 ;
const double expr_1924920005 = (expr_2798091491 <= expr_2831327593)? 0: fp64_dis(expr_2798091491,expr_2831327593);
const double expr_2883938295 = expr_1586913185 + expr_1168251917 + expr_1542123215 + expr_1924920005;
return expr_2883938295;
}


double (unsigned n, const double * x, double * grad, void * data){ 
const double expr_1010793773 = Unsupported expr:a_ack!1
const double expr_165672123 = expr_1010793773;
const double expr_3577401711 = 0x3ff0000000000000 ;
const double expr_3303468021 = expr_3577401711;
const double expr_754533101 = fp64_dis(expr_165672123,expr_3303468021);
const double expr_3329830049 = Unsupported expr:b_ack!2
const double expr_1133087327 = expr_3329830049;
const double expr_2144113661 = 0x0000000000000000 ;
const double expr_2449201227 = expr_2144113661;
const double expr_3293811629 = fp64_dis(expr_1133087327,expr_2449201227);
const double expr_2919235499 = expr_754533101 + expr_3293811629;
return expr_2919235499;
}


