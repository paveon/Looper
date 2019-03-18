#include <stdlib.h>
#include <stdio.h>

//Complexity: n
void foo(uint n) {
	int x = n;
	while (x > 0) {
		int y = x - 1;
		while (y > 0) {
			y--;
		}
		x = y;
	}
}