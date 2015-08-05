/*
 * Includes
 */
#include <stdbool.h>
#include <stdlib.h>

/*
 * Preloaded Code
 */
typedef struct SPLArray {
  int length;
  void* arr[];
} SPLArray;

void freeSPLArray (SPLArray* a) {
  free(a->arr);
  free(a);
}

/*
 * Procedures
 */
int proc0_1 (int a_3);

int proc1_1 (int a_4);

int proc2_1 (int a_5);

int proc0_1 (int a_3) {
  int b_12;
  if (a_3 == 0) {
    b_12 = 0;
  } else {
    tmp_2 = proc0_1(a_3 - 1);
    b_12 = a_3 + tmp_2;
  }
  return b_12;
}

int proc1_1 (int a_4) {
  int b_13;
  if (a_4 == 0) {
    return 0;
  } else {
    b_13 = proc2_1(a_4);
    return b_13;
  }
  return b_13;
}

int proc2_1 (int a_5) {
  int b_14;
  if (a_5 < 0) {
    b_14 = proc1_1(a_5 + 1);
    return b_14;
  } else {
    b_14 = proc1_1(a_5 - 1);
    return b_14;
  }
  return b_14;
}