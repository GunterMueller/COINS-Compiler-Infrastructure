/* fileWrite1.c */
/* Write BUFSIZE bytes to stdout file by write */
/* Usage:
    ./a.exe 2> outfile
*/ 
#include <stdio.h>
/*
#define BUFSIZE 8192
#define COUNT 10000
*/
#define BUFSIZE 16
#define COUNT   10

char buffer[BUFSIZE];

int main( int argc, char *argv[])
{
  int i, nbyte;
  FILE *fp;
  for (i = 0; i < BUFSIZE; i++)
    buffer[i] = '0'+i%10;
  for (i = 0; i < COUNT; i++) {
    nbyte = write(1, buffer, BUFSIZE);
  }
  printf("write %d bytes %d times to stdout by write(....) \n", BUFSIZE, COUNT);
}
