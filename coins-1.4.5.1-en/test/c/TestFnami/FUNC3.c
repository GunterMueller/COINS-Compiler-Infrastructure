int printf(char *s, ...);

void f(int x1,int x2,int x3,int x4,int x5,int x6,int x7) {
  printf("%d %d %d %d %d %d %d\n",x1,x2,x3,x4,x5,x6,x7);
}

int main() {
  f(1,2,3,4,5,6,7);
  return 0;
}
