/* tpprintf2.c:  printf without declaration */

/* int printf(char* pForm, ...); */

int main()
{
  int i = 1, j;

  j = i + 1;
  printf("i %d j %d \n", i, j);
  return 0;
} 

