//Complexity: (n + 1) * max(n - 1, 0) + n + 1
void SingleLinkSimple(uint n) {
	int a = n;
	int b = 1;
	while (b > 0) {
		for (int i = n - 1; i > 0; i--) {
			if (a > 0) {
				a--;
				b++;
			}
		}
		b--;
	}
}