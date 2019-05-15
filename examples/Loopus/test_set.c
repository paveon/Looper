int while_unique_def_FN(int p) {
  int j = 0;
  while (j < 10) {
    if (p > 0) {
      j = 500;
    } else {
      j = -1;
    }
  }
  return 0;
}

/* Theta(n) */
void do_k_times(int n) {
  int k = n;
  for (int i = 0; i < k; i++) {
  }
}

/* Theta(n) */
void do_k_times_array(int n) {
  int k = n;
  int a[10];
  for (int i = 0; i < k; i++) {
    a[k] = 4 + k;
  }
}

/* Expected Theta(n * m) */
void do_n_m_times_nested(int n, int m) {
  int k = n;
  int p = m;
  for (int i = 0; i < k; i++) {
    for (int j = 0; j < p; j++) {
    }
  }
}

/* Expected ~ 3 * p. Also inner loop will have t as invariant */
void two_loops_nested_invariant(int p) {
  int t = 0;
  int m = p;
  for (int i = 0; i < m; i++) {
    t = 3;
    for (int j = 0; j < t; j++) {
    }
  }
}

/* since the guard i is invariant, we will remove it from control
   variables, and hence the total cost will be constant, but the
   program diverges */
int while_infinite_FN() {
  int i = 0;
  while (i < 10) {
  }
  return 0;
}


int if_in_loop(int t) {
  int p = 0;
  int j = t + 1;
  for (int i = 0; i < 5; i++) {
    if (j < 2) {
      p++;
    } else {
      p = 3;
      for (int k = 0; k < 10; k++) {
        int m = 0;
      }
    }
  }
  return p;
}

// j is not a control var, so shouldn't affect the bound
int if_out_loop(int t) {
  int p = 10;
  int j = t + 10;
  if (j < 2) {
    p++;
  } else {
    p = 3;
    for (int k = 0; k < 100; k++) {
      int m = 0;
    }
  }
  return p;
}

int do_while_independent_of_p(int p) {
  int a = 0;
  do {
    if (p == 15) {
      p = p + 1;
    }
    a++;
  } while (a < 25);

  return 0;
}

void larger_state_FN() {

  int i = 0, k = 0;
  while (k < 100) {
    i++;
    if (i >= 10000) {
      k++;
      i = 0;
    }
  }
}

static int array1[] = {1, 2, 3};
static int array2[] = {};

// Cvars will initially contain array1 and array2 but will be removed
// since they are invariant
void loop_use_global_vars(int x) {
  for (int i = 0; i < x && array1 != array2; i++) {
    // do something
  }
}

void ptr_cmp(char* end, int size) {
  char buf[2] = "hi";
  for (int i = 0; i < size; i += 2) {
    if (buf < end) { // pvar &buf occurs directly in prune node
      return;
    }
  }
}

int compound_while(int m) {
  int i = 0;
  int j = 3 * i;
  while (j == 0 && i < m) {
    i++;
  }
  return j;
}

// Loop's execution count doesn't depend on values of p,t,k
int loop_no_dep1(int k) {
  int p = 0;
  int t = 2 + k;
  for (int i = 0; i < 100; i++) {
    p++;
  }
  return p;
}

int foo(int i, int j) { return i + j; }

// Loop's execution count doesn't depend on values of p,t,k
int loop_no_dep2(int k) {
  int p = 0;
//   int t = foo(p, k);
  for (int i = 0; i < 100; i++) {
    p++;
  }
  return p;
}

// -- Below examples didn't work before, but enhancing CF analysis
// makes the analysis much more precise and we can get proper bounds
//
// This example works now because even though j in [-oo.+oo],
// since control vars={k} (notice that we will remove {p,j} in the else branch),
// we ignore j and find the right bound for the inner loop
int if_bad(int j) {
  int p = 10;
  if (p < 10 + j) {
    p++;
  } else {
    p = j + 3;
    for (int k = 0; k < 10; k++) {
      j += 3;
    }
  }
  return p;
}

// Notice that removing {j,p} above doesn't create any problems if we are in a
// loop that depends on them. E.g.: below we still depend on {j} but in the
// conditional prune statement, we will remove the temp. var that map to inner
// {j}, not the outer {j}
int if_bad_loop() {
  int p = 10;
  for (int j = 0; j < 5; j++) {
    if (j < 2) {
      p++;
    } else {
      p = 3;
      for (int k = 0; k < 10; k++) {
        int m = 0;
      }
    }
  }
  return p;
}

// The fake dependency btw first and second loop disappeared and we can get a
// proper bound
//
int two_loops() {
  int p = 10;
  int k = 3;
  int t = 2 + k;
  for (int j = 0; j < 6; j++) {
    k++;
  }
  for (int i = 0; i < 100; i++) {
    p = 3;
  }
  return p;
}

// We don't get a false dependency to m (hence p) since
// for if statements, we don't add prune variables as dependency
int loop_despite_inferbo(int p) {

  int k = 100;
  for (int i = 0; i < k; i++) {
    int m = p + 3;
    if (m < 14) {
      p += 9;
    }
  }
  return p;
}

/* Expected: 5 * 100 */
int nested_loop() {
  int k = 0;
  for (int i = 0; i < 5; i++) {
  A:
    k = 0;
    for (int j = 0; j < 100; j++) {
      k = 3;
    }
  }
  return k;
}


int real_while() {
  int i = 0;
  int j = 3 * i;
  while (i < 30) {
    j = j + i;
    i++;
  }
  return j;
}


void nop() { int k = 0; }

// Expected: Theta(m)
int two_loops_symb(int m) {
  int p = 10;

  for (int i = 0; i < m; i++) {
    nop();
  }
  for (int j = 0; j < m; j++) {
    nop();
  }
  return p;
}

// Expected: Theta(m + k)
int two_loops_symb_diff(int m, int k) {
  int p = 10;
  for (int i = 0; i < m; i++) {
    nop();
  }
  for (int j = 0; j < k; j++) {
    nop();
  }
  return p;
}

// Cost: 6
void alias2_OK() {

  int i, j, z;

  j = 1;
  z = 2;

  j = i;
  i = z;
}

// Cost: 1004
int loop0_bad() {

  for (int i = 0; i < 100; i++) {
    alias2_OK();
  }
  return 0;
}

// Cost: 1006
int loop1_bad() {

  int k = 100;
  for (int i = 0; i < k; i++) {
    alias2_OK();
  }
  return 0;
}

// Expected: Theta(k)
int loop2_bad(int k) {

  for (int i = 0; i < k; i++) {
    alias2_OK();
  }
  return 0;
}

// Expected: ~15
int loop3_bad(int k) {

  for (int i = k; i < k + 15; i++) {
    alias2_OK();
  }
  return 0;
}



/* p should be in control vars */
void while_and_or(int p) {
  int i = 0;
  while (p == 1 || (i < 30 && i >= 0)) {
    i++;
  }
}

// should be constant cost
int nested_while_and_or(int p) {
  int i = 0;
  int j = 3 * i;
  while (p == 1 || (i < 30 && i >= 0)) {
    while (p == 1 || (j < 5 && j >= 0)) {

      return j;
    }
    i++;
  }
  return j;
}


void infinite() {
  int z;
  for (int i = 0; i % 2 == (i + 2) % 2; i++) {
    z += i;
  }
}