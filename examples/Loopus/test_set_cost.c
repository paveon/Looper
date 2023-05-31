#include <stdint.h>

/* t is also in control variables but once we have invariant analysis, it
 * shouldn't be */
// [p]
int break_loop(int p, int t) {
  for (int i = 0; i < p; i++) {
    // do something
    if (t < 0)
      break;
    // do something
  }
  return 0;
}

/* t will be in control variables but once we have invariant analysis,
 * it shouldn't be. */
// [p]
int break_loop_with_t(int p, int t) {
  for (int i = 0; i < p; i++) {
    // do something
    if (t < 0) {
      t++;
      break;
    }
    // do something
  }
  return 0;
}

/* calling break_loop with a negative t should give constant
   cost. Currently, this doesn't work since we can't do case analysis
   on the domain. */
// 1
int break_constant_FP(int p) { return break_loop(p, -1); }

/* while loop that contains && in the guard. It gives the correct bound.
 * Expected: O(m)  */
int compound_while(int m) {
  int i = 0;
  int j = 3 * i;
  while (j == 0 && i < m) {
    i++;
  }
  return j;
}

int simplified_simulated_while_with_and_constant(int p) {
  int k = 0;
  int j = 0;
B:
  j++;
  if (k == 0 && j < 100) {
    goto B; // continue;
  }
  return k;
}

// int do_while_test(int p) {
//   int k = 0;
//   int j = 0;
//   do {
//     j++;
//   } while (k == 0 && j < 100);
//   return k;
// }

// //[Final bound] 1100
// int double_do_while_test(int p) {
//   int k = 0;
//   int j = 0;
//   do {
//     j++;
//     int x = 0;
//     do {
//       x++;
//     } while (x < 10);
//   } while (k == 0 && j < 100);
//   return k;
// }

// //[Final bound] 1100
// int while_test(int p) {
//   int k = 0;
//   int j = 0;
//   while (k == 0 && j < 100) {
//     j++;
//     int x = 0;
//     while (x < 10) {
//       x++;
//     }
//   }
//   return k;
// }

/* simulated goto that contains && */
int simulated_while_with_and_linear(int p) {
  int i = 0;
  int k = 0;
LOOP_COND:
  if (k == 0 && i < p) { // k == 0 always true
    goto INCR;
  } else {
    goto RETURN;
  }
INCR:
  i++;
  goto LOOP_COND;
RETURN:
  return i;
}

/* shortcut in the conditional, hence we won't loop, and get constant cost */
int simulated_while_shortcut_constant(int p) {
  int k = 0;
  int j = 0;
B:
  j++;
  if (k == 1 && j < 100) {
    goto B; // continue;
  }
  return k;
}

/* p should be in control vars. If p is 1, can run forever */
// For now the implication "p == 1 || (i < 30 && i >= 0) => (30 - i) > 0"
// does not hold so "(30 - i) > 0" is not derived as a guard and thus
// the decrement is eliminated and no local bound is found. We would have
// to implement some sort of multiple-case pre-conditions to support cases
// like this. For now we return INF which is technically right but not very
// precise.
void while_and_or(int p) {
  int i = 0;
  while (p == 1 || (i < 30 && i >= 0)) {
    i++;
  }
}

// should be constant cost
int nested_while_and_or_constant(int p) {
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

/* j and i will be control variables for B  */
int simulated_nested_loop_with_and_constant(int p) {
  int k = 0;
  int t = 5;
  int j = 0;
  for (int i = 0; i < 5; i++) {
  B:
    t = 3;
    j++;
    if (k == 0 && j < 100) { // k == 0 always true
      goto B; // continue;
    }
  }
  return k;
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
  int t = foo(p, k);
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
int if_bad_constant(int j) {
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
int if_bad_loop_constant() {
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
int loop_despite_inferbo_constant(int p) {

  int k = 100;
  for (int i = 0; i < k; i++) {
    int m = p + 3;
    if (m < 14) {
      p += 9;
    }
  }
  return p;
}

int nested_loop_constant() {
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

// Unlike the above program, B will be inside the inner loop, hence executed
// around 105 times
int simulated_nested_loop_constant(int p) {
  int k = 0;
  int t = 5;
  int j = 0;
  for (int i = 0; i < 5; i++) {
  B:
    t = 3;
    j++;
    if (j < 100)
      goto B; // continue;
  }
  return k;
}

// B will be inside the inner loop and executed ~500 times
int simulated_nested_loop_more_expensive_constant(int p) {
  int k = 0;
  int t = 5;
  int j = 0;
  for (int i = 0; i < 5; i++) {
  B:
    t = 3;
    j++;
    if (j < 100)
      goto B; // continue;
    else {
      j = 0;
    }
  }
  return k;
}

int real_while_constant() {
  int i = 0;
  int j = 3 * i;
  while (i < 30) {
    j = j + i;
    i++;
  }
  return j;
}

// Examples with gotos

/* The following program is the version of real_while() with gotos */

int simulated_while_constant() {
  int i = 0;
  int j = 3 * i;
LOOP_COND:
  if (i < 30) {
    goto INCR;
  } else {
    goto RETURN;
  }
INCR:
  j = j + i;
  i++;
  goto LOOP_COND;
RETURN:
  return j;
}

/* Conditional inside goto loop  */
/* Expected: 5 * 100 */
int simulated_nested_loop_cond_in_goto_constant(int p) {
  int k = 0;
  int t = 5;
  int j = 0;
  for (int i = 0; i < 5; i++) {
  B:
    if (i > 2) {
      t = 3;
    } else {
      t = 4;
    }
    j++;
    if (j >= 100)
      j = 0;
    else {
      goto B; // continue;
    }
  }
  return k;
}

int foo_constant() {
  int i, j;
  i = 17;
  j = 31;
  return i + j + 3 + 7;
}

int cond_constant(int i) {
  int x;

  if (i < 0) {
    x = foo_constant();
  } else {
    x = 1;
  }
  return x;
}

int loop0_constant() {

  for (int i = 0; i < 100; i++) {
    foo_constant();
  }
  return 0;
}

int loop1_constant() {

  int k = 100;
  for (int i = 0; i < k; i++) {
    foo_constant();
  }
  return 0;
}

// Expected: O(k)
int loop2_linear(int k) {

  for (int i = 0; i < k; i++) {
    alias2();
  }
  return 0;
}

int loop3_constant(int k) {

  for (int i = k; i < k + 15; i++) {
    alias2();
  }
  return 0;
}

// Expected: O(20-m)
int while_upto20(int m) {
  while (m < 20) {
    int l = 0;
    m++;
  }
  return m;
}

void call_while_upto20_minus100_constant() { while_upto20(-100); }

void call_while_upto20_10_constant() {
  for (int i = 0; i < 10; i++) {
    while_upto20(10);
  }
}

void call_while_upto20_unsigned(unsigned x) { while_upto20(x); }

// Cost: 1
void unit_cost_function() {}

int always(int i) { return i % 2 == (i + 2) % 2; }

void infinite_FN() {
  int z;
  for (int i = 0; always(i) != 0; i++) {
    z += i;
  }
  int x = 5;
  for (int i = 0; i < 5; i++) {
    if (i < 2) {
      x = 10;
    } else {
      x = 5;
    }
  }
}

void infinite() {
  int z;
  for (int i = 0; i % 2 == (i + 2) % 2; i++) {
    z += i;
  }
}

void call_infinite() { infinite(); }

void loop_character_symbols_linear(char c) {
  for (; c < 'z';) {
    if (rand()) {
      c = 'a';
    }
  }
}

unsigned int div_const(unsigned int n) { return n / 2; }

void iter_div_const_constant() {
  unsigned int n = div_const(20);
  for (int i = 0; i < n; i++) {
  }
}

void exit_unreachable() {
  exit(0); // modeled as unreachable
}

// constraint solver resolves all nodes to unreachable cost
void compute_exit_unreachable() {
  int k = 0;
  exit(0);
}

// [p]
void linear(int p) {
  for (int i = 0; i < p; i++) {
  }
}

void call_exit_unreachable(int p) {
  linear(p);
  exit(0);
}

// constraint solver doesn't behave consistently and gets confused
// when resolving constraints and gets linear cost
void inline_exit_unreachable_FP(int p) {
  for (int i = 0; i < p; i++) {
  }
  exit(0);
}

void call_unreachable() { exit_unreachable(); }

void no_op() { int x = 0; }

// Expected: O(n)
void do_n_times(int n) {
  for (int i = 0; i < n; i++) {
    no_op();
  }
}

void do_2_times_constant() { do_n_times(2); }

// Expected: O(m^2)
void do_m2_times_quadratic(int m) {
  for (int i = 0; i < m; i++) {
    do_n_times(m);
  }
}

// Expected: O(m^2)
void do_half_m2_times_quadratic(int m) {
  for (int i = 0; i < m; i++) {
    do_n_times(i);
  }
}

/* Depending on whether p is positive, the program might loop forever */
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

/* Expected O(n * m) */
void do_n_m_times_nested(int n, int m) {
  int k = n;
  int p = m;
  for (int i = 0; i < k; i++) {
    for (int j = 0; j < p; j++) {
    }
  }
}

/* Expected:O(p). Also inner loop will have t as invariant */
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

/* With the dominator approach, we can't find any back-edges here
   since there are two entry points to the loop and there is no single
   back edge to a single loop entry point, but only to the beginning
   of the Loop label. With Tarjan's DFS approach, we can identify the
   back-edge to the Loop label, and we are able to detect two
   exit-edges correctly.
 */
int loop_always_linear(int p, int k) {
  int i = 0;
  if (p > 0) {
    goto Loop;
  }

  while (i < k) {
  Loop:
    i++;
  }
  return 1;
}

void do_while_test(int k) {
  int i = 0;
  do {
    i++;
  } while (i < k);
}

int jump_inside_loop_constant_linear(int p, int k) {
  int i = 0;
  if (p > 0) {
    goto Loop;
  } else {
    return p;
  }
  while (i < k) {
  Loop:
    i++;
  }
  return 1;
}

// j is not a control var, so shouldn't affect the bound
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

// void simple_loop(int n) {
//   int i = n;
//   while (i > 0) {
//     foo(i);
//     i--;
//   }
// }

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

void test(int x) {
  for (int i = 0; i < x; i++) {
  }
}

// just to sanity check that we don't fail on cost with purity analysis enabled
int loop(int k) {
  void (*fun_ptr)(int) = test;
  int p = 0;
  for (int i = 0; i < 1000; i++) {
    p = 3;
    (*fun_ptr)(10);
  }
  return p;
}

int test_switch_FN() {
  int value = 0;
  // infinite loop
  while (value < 100) {
    switch (value) {
      // code before the first case statement gets skipped but can be used to
      // declare variables
      int x = 1;
      x = value + 1;
      case 0:
        break;
      case 1:
        continue;
      case 2:
      default:
        continue;
    }
    value++;
  }
  return 0;
}

int unroll_loop(int n) {
  int ret = 0;
  int loop = n + 3 / 4;
  switch (n % 8) {
    case 0:
      do {
        ret++;
        case 3:
          ret++;
          if (1) {
            case 2:
              ret++;
          }
        case 1:
          ret++;
      } while (--loop > 0);
  }
  return ret;
}

void nop() { int k = 0; }

// Expected: O(m)
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

// Expected: O(m + k)
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
