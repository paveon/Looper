#include <stdlib.h>
#include <stdio.h>


//Complexity: n
void bar(uint n) {
	int x = n;
	while (x > 0) {
		int y = x - 1;
		while (y > 0) {
			y--;
		}
		x = y;
	}
}

//Complexity: 2n
void foo(uint n) {
	int x = n;
	int r = n;
	while(x > 0) {
        x--;
		if(n == 42) {
			int p = r;
			while(p > 0) {
				p--;
			}
			r = 0;
		}
	}
}

//Complexity: 4n
void foobar(uint n) {
	int x = n;
	int y = n;
	int p = 0;
	while(x > 0) {
        x--;
		int r = 0;
		while (y > 0) {
			y--;
			r++;
		}
		if (n == 54) {
			p = r;
		}
		while (p > 0) {
			p--;
		}
		p = r;
	}
}

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

//Complexity: 2n
void tarjan(uint n) {
	uint i = n;
  uint j = 0;
	while (i > 0) {
		i--;
		j++;
		while (j > 0) {
			j--;
		}
	}
}

//Complexity: 3n + max(m1,m2)
void twoSCCs(uint n, uint m1, uint m2) {
	int y = n;
	int x = 0;
	if(m2 == 42) {
		x = m1;
	} 
	else {
		x = m2;
	}
	while(y > 0) {
		y--;
		x = x + 2;
	}

	int z = x;
	while(z > 0) {
		z--;
	}
}


//Complexity: 2n
void xnu(uint n) {
	int beg = 0;
	int end = 0;
	int i = 0;
	while(i < n) {
		i++;
		if (n == 42) //L2
			end = i;
		// L3
		if (n == 24) { //L4
			int k = beg;
			while (k < end) {
				k++;
			}
			end = i;
			beg = end;
		} else {
			if(n == 54) {
				end = i;
				beg = end;
			}
		}
	}
}


//Complexity: 2n
void xnuSimple(uint n) {
	int x = n;
	int r = 0;
	while(x > 0) {
    x--;
		r++;
		if(n == 42) {
			int p = r;
			while(p > 0) {
				p--;
			}
			r = 0;
		}
	}
}