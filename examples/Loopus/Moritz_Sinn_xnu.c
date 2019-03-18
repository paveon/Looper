#include <stdlib.h>
#include <stdio.h>

//Complexity: 2n
void xnu(uint n) {
	int beg = 0;
	int end = 0;
	int i = 0;
	while(i < n) {
		i++;
		if (4) //L2
			end = i;
		// L3
		if (5) { //L4
			int k = beg;
			while (k < end) {
				k++;
			}
			end = i;
			beg = end;
		} else {
			if(6) {
				end = i;
				beg = end;
			}
		}
	}
}