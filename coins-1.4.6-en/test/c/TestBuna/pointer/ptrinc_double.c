int printf(char* f, ...);

int main(int argc, char **argv) {
  double data[6];
  double *p;
  double n;

  data[0] = 1.1;
  data[1] = 2.2;
  data[2] = 3.3;
  data[3] = 4.4;
  data[4] = 5.5;
  data[5] = 0.0;
  

  for(n=0, p=data; *p > 0; ++p) {
    n += *p;
  }
  printf("answer=%f\n", n);
}
