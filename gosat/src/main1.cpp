/**
  (define-fun a () (_ FloatingPoint 8 24) (fp #b1 #b11111111 #b00000000000000000000000))
  (define-fun b () (_ FloatingPoint 8 24) (fp #b0 #b11111111 #b00000000000000000000000))
  (define-fun n () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b00000000000000000000000))

 */

#include <stdio.h>
int main() {
    int int_a = 0xff000000;
    int int_b = 0xff000000;
    int int_n = 0x7f000000;
  float *a = (float *)&int_a;
  float *b = (float *)&int_b;
  float *n = (float *)&int_n;
    printf("a=%f,b=%f,n=%f\n",*a,*b,*n);
    printf("nb=%f\n",*n * *b);
  if(*a<*n * *b){
      printf("1\n");
      if(*b>0){
          printf("2\n");
          if(*a / *b>*n){
              printf("3\n");
              printf("true::a=%f,b=%f,n=%f\n",*a,*b,*n);
          }
      }
  }
}