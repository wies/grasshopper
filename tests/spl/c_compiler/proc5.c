/*
 * Includes
 */
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

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
 * Structs
 */
struct Node_1;

typedef struct Node_1 {
  int data_1;
  struct Node_1* next_1;
} Node_1;

/*
 * Procedures
 */
struct SPLArray* arrayOfSquares_1 (int n_10);
struct SPLArray* getLessThan_1 (struct SPLArray* a_16, int n_11);

struct SPLArray* arrayOfSquares_1 (int n_10) {
  struct SPLArray* a_15;
  struct SPLArray* tmp_6;
  int i_20;
  
  tmp_6 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * n_10));
  tmp_6->length = n_10;
  {
    for (int i = 0; i < n_10; i++) {
      (tmp_6->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  
  a_15 = tmp_6;
  i_20 = 0;
  while (true) {
    if (!((i_20 < n_10))) {
      break;
    }
    *(((int**) (a_15->arr))[i_20]) = ((i_20 + 1) * (i_20 + 1));
    i_20 = (i_20 + 1);
  }
  return a_15;
}

struct SPLArray* getLessThan_1 (struct SPLArray* a_16, int n_11) {
  struct SPLArray* b_6;
  struct SPLArray* tmp_8;
  struct SPLArray* tmp_7;
  int j_7;
  struct SPLArray* isLess_10;
  int i_21;
  int count_7;
  
  tmp_7 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * (a_16->length)));
  tmp_7->length = (a_16->length);
  {
    for (int i = 0; i < (a_16->length); i++) {
      (tmp_7->arr)[i] = (bool*) malloc(sizeof(bool));
    }
    
  }
  
  isLess_10 = tmp_7;
  count_7 = 0;
  i_21 = 0;
  while (true) {
    if (!((i_21 < (a_16->length)))) {
      break;
    }
    if ((*(((int**) (a_16->arr))[i_21]) < n_11)) {
      *(((bool**) (isLess_10->arr))[i_21]) = true;
      count_7 = (count_7 + 1);
    } else {
      *(((bool**) (isLess_10->arr))[i_21]) = false;
    }
    i_21 = (i_21 + 1);
  }
  tmp_8 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * count_7));
  tmp_8->length = count_7;
  {
    for (int i = 0; i < count_7; i++) {
      (tmp_8->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  
  b_6 = tmp_8;
  i_21 = 0;
  j_7 = 0;
  while (true) {
    if (!((i_21 < (a_16->length)))) {
      break;
    }
    if (*(((bool**) (isLess_10->arr))[i_21])) {
      *(((int**) (b_6->arr))[j_7]) = *(((int**) (a_16->arr))[i_21]);
      j_7 = (j_7 + 1);
    }
    i_21 = (i_21 + 1);
  }
  return b_6;
}

/*
 * Main Function, here for compilability
 */
int main() {
  SPLArray* a = arrayOfSquares_1(10);
  SPLArray* b = getLessThan_1(a, 50);
  
  for (int i = 0; i < (a->length); i++) {
    printf("%d\n", *((int*) (a->arr)[i]));
  }

  for (int i = 0; i < (b->length); i++) {
    printf("%d\n", *((int*) (b->arr)[i]));
  }
  return 0;
}
