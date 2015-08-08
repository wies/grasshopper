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
 * Structs
 */
struct SillyStruct_1;
struct SuperSillyStruct_1;

typedef struct SillyStruct_1 {
  int a_13;
} SillyStruct_1;

typedef struct SuperSillyStruct_1 {
  struct SPLArray* arr_2;
} SuperSillyStruct_1;

/*
 * Procedures
 */
void procAssign_1 ();
void procBlock_1 (int* a_15, bool* b_7, int* c_7);
void procDispose_1 (struct SPLArray* a_16, struct SillyStruct_1* b_8);
bool procIf_1 (int a_17, int b_9);
void procLoop_1 ();
struct SPLArray* procNewArray_1 ();
int procReturn_1 ();

void procAssign_1 () {
  int z_4;
  bool y_4;
  int x_5;
  struct SPLArray* tmp_19;
  struct SillyStruct_1* tmp_18;
  struct SPLArray* b_6;
  struct SillyStruct_1* a_14;
  
  tmp_18 = ((struct SillyStruct_1*) malloc(sizeof(struct SillyStruct_1)));
  a_14 = tmp_18;
  tmp_19 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 10));
  tmp_19->length = 10;
  {
    for (int i = 0; i < 10; i++) {
      (tmp_19->arr)[i] = (bool*) malloc(sizeof(bool));
    }
    
  }
  
  b_6 = tmp_19;
  
  
  
  procBlock_1(&x_5, &y_4, &z_4);
  x_5 = (1 + 1);
  y_4 = true;
  z_4 = ((700 * 6) / 2);
  x_5 = 100;
}

void procBlock_1 (int* a_15, bool* b_7, int* c_7) {
  (*a_15) = 1;
  (*a_15) = 2;
  (*a_15) = 3;
  (*b_7) = false;
  (*c_7) = (-2000);
}

void procDispose_1 (struct SPLArray* a_16, struct SillyStruct_1* b_8) {
  struct SPLArray* tmp_25;
  struct SPLArray* tmp_24;
  struct SPLArray* tmp_23;
  struct SPLArray* tmp_22;
  struct SuperSillyStruct_1* tmp_21;
  struct SPLArray* tmp_20;
  struct SPLArray* d_2;
  struct SuperSillyStruct_1* c_8;
  
  freeSPLArray(a_16);
  
  free(b_8);
  
  tmp_20 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 5));
  tmp_20->length = 5;
  {
    for (int i = 0; i < 5; i++) {
      (tmp_20->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  
  freeSPLArray(tmp_20);
  
  tmp_21 = ((struct SuperSillyStruct_1*) malloc(sizeof(struct SuperSillyStruct_1)));
  c_8 = tmp_21;
  tmp_22 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 10));
  tmp_22->length = 10;
  {
    for (int i = 0; i < 10; i++) {
      (tmp_22->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  
  (c_8->arr_2) = tmp_22;
  freeSPLArray((c_8->arr_2));
  
  free(c_8);
  
  tmp_23 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 5));
  tmp_23->length = 5;
  {
    for (int i = 0; i < 5; i++) {
      (tmp_23->arr)[i] = (struct SPLArray*) malloc(sizeof(struct SPLArray));
    }
    
  }
  
  d_2 = tmp_23;
  tmp_24 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 5));
  tmp_24->length = 5;
  {
    for (int i = 0; i < 5; i++) {
      (tmp_24->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  
  (((struct SPLArray**) (d_2->arr))[0]) = tmp_24;
  freeSPLArray((((struct SPLArray**) (d_2->arr))[0]));
  
  freeSPLArray(d_2);
  
  tmp_25 = procNewArray_1();
  freeSPLArray(tmp_25);
  
}

bool procIf_1 (int a_17, int b_9) {
  bool c_9;
  if ((a_17 == b_9)) {
    c_9 = true;
  } else {
    c_9 = false;
  }
  return c_9;
}

void procLoop_1 () {
  int i_7;
  
  i_7 = 0;
  while (true) {
    if (!((!(i_7 == 5)))) {
      break;
    }
    i_7 = (i_7 + 1);
  }
}

struct SPLArray* procNewArray_1 () {
  struct SPLArray* a_18;
  struct SPLArray* tmp_26;
  
  tmp_26 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 10));
  tmp_26->length = 10;
  {
    for (int i = 0; i < 10; i++) {
      (tmp_26->arr)[i] = (bool*) malloc(sizeof(bool));
    }
    
  }
  
  return tmp_26;
  return a_18;
}

int procReturn_1 () {
  int a_19;
  return 5;
}

/*
 * Main Function, here for compilability
 */
int main() {
  return 0;
}
