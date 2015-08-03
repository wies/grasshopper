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
void proc1_1 (int a_1, bool b_1, int* ap_2, bool* bp_2);

void proc1_1 (int a_1, bool b_1, int* ap_2, bool* bp_2) {
  (*ap_2) = a_1;
    (*bp_2) = b_1;
}