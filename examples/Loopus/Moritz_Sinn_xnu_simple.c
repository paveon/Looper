#include <stdlib.h>
#include <stdio.h>

//Complexity: 2n
void xnuSimple(uint n) {
	int x = n;
	int r = 0;
	while(x > 0) {
        x--;
		r++;
		if(0) {
			int p = r;
			while(p > 0) {
				p--;
			}
			r = 0;
		}
	}
}