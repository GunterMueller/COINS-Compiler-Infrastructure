/* for_01 simple for statement */
int printf(char *s, ...);

int main() {
	int a, i;
	a = 0;
	for (i = 0; i < 5; i++) {
		a += 10;
		printf("i = %d\n", i);
	}
	return 0;
}