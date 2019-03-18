#include <stdlib.h>
#include <stdio.h>

//Complexity: (n + 1) * max(n - 1, 0) + n + 1
void SingleLinkSimple(uint n) {
	int a = n;
	int b = 0;
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