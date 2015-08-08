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
void proc1_1 ();
void proc2_1 (int a_6);
void proc3_1 (int a_7, int b_3);
int proc4_1 ();
int proc5_1 (int a_8);
int proc6_1 (int a_9, int b_4);
void proc7_1 (int* ar_16, int* br_6);
void proc8_1 (int a_10, int* ar_17, int* br_7);
void proc9_1 (int a_11, int b_5, int* ar_18, int* br_8);

void proc1_1 () {
  
}

void proc2_1 (int a_6) {
  
}

void proc3_1 (int a_7, int b_3) {
  
}

int proc4_1 () {
  int ar_13;
  ar_13 = 4;
  return ar_13;
}

int proc5_1 (int a_8) {
  int ar_14;
  ar_14 = a_8;
  return ar_14;
}

int proc6_1 (int a_9, int b_4) {
  int ar_15;
  ar_15 = a_9;
  ar_15 = b_4;
  return ar_15;
}

void proc7_1 (int* ar_16, int* br_6) {
  (*ar_16) = 4;
  (*br_6) = 5;
}

void proc8_1 (int a_10, int* ar_17, int* br_7) {
  (*ar_17) = a_10;
  (*br_7) = 5;
}

void proc9_1 (int a_11, int b_5, int* ar_18, int* br_8) {
  (*ar_18) = a_11;
  (*br_8) = b_5;
}

/*
 * Main Function, here for compilability
 */
int main() {
  return 0;
}
