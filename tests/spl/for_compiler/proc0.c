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
void proc1_1 (int a_1, bool b_1, int* ap_1, bool* bp_1);

void proc1_1 (int a_1, bool b_1, int* ap_1, bool* bp_1) {
  f_2 = 0;
  g_2 = 0;
  i_2 = 0;
  j_2 = 0;
  k_2 = 0;
}