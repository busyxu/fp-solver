int main() {
float a,b,c;
klee_make_symbolic(&a, sizeof(a), "a");
klee_make_symbolic(&b, sizeof(b), "b");
klee_make_symbolic(&c, sizeof(c), "c");

if (cos(a) > log(b)){
  if (sin(a) < log(b)){
    c = c -1.0;
    if (c == 1.1)
      printf("Neve reach here !\n");
    }
  }
  return 0;
}
