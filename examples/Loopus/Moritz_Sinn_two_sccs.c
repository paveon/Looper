//Complexity: 3n + max(m1,m2)
void twoSCCs(uint n, uint m1, uint m2) {
	int y = n;
	int x = 0;
	if(0) {
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