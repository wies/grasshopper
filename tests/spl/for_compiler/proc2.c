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
struct SPLArray* copy_1 (struct SPLArray* a_28);
void procCall_1 (int* a_29, bool* b_19);
void procIntAndBoolVal_1 (int* a_30, bool* b_20);
int procNull_1 ();
void procOps_1 (int a_32, int b_21, bool c_7, bool d_1, int* ap_6, int* bp_3, bool* cp_2, bool* dp_2);
struct SPLArray* procReadLengthNew_1 ();

struct SPLArray* copy_1 (struct SPLArray* a_28) {
  struct SPLArray* b_18;
  struct SPLArray* tmp_4;
  int i_27;
  
  tmp_4 = (struct SPLArray*) malloc(sizeof(struct SPLArray));
  tmp_4->length = (a_28->length);
  {
    for (int i = 0; i < (a_28->length); i++) {
      *((tmp_4->arr) + i) = (int*) malloc(sizeof(int));
    }
    
  }
  
  b_18 = tmp_4;
  i_27 = 0;
  while (true) {
    
    if (!((i_27 < (a_28->length)))) {
      break;
    }
    *(((int**) (b_18->arr))[i_27]) = *(((int**) (a_28->arr))[i_27]);
    i_27 = (i_27 + 1);
  }
  return b_18;
}

void procCall_1 (int* a_29, bool* b_19) {
  
  
  procIntAndBoolVal_1(&(*a_29), &(*b_19));
  *a_29 = (*a_29);
  *b_19 = (*b_19);
  return;
}

void procIntAndBoolVal_1 (int* a_30, bool* b_20) {
  
  
  (*a_30) = 1;
  (*a_30) = (-1);
  (*a_30) = 0;
  (*a_30) = 277;
  (*b_20) = true;
  (*b_20) = false;
}

int procNull_1 () {
  int a_31;
  
  
  if ((NULL == NULL)) {
    a_31 = 1;
  } else {
    a_31 = 0;
  }
  return a_31;
}

void procOps_1 (int a_32, int b_21, bool c_7, bool d_1, int* ap_6, int* bp_3, bool* cp_2, bool* dp_2) {
  
  
  (*ap_6) = a_32;
  (*bp_3) = b_21;
  (*cp_2) = c_7;
  (*dp_2) = d_1;
  (*ap_6) = (-(*ap_6));
  if ((!(*dp_2))) {
    
  } else {
    
  }
  (*ap_6) = ((*ap_6) + (*bp_3));
  (*bp_3) = ((*ap_6) - (*bp_3));
  (*ap_6) = ((*ap_6) * (*bp_3));
  (*ap_6) = ((*ap_6) / (*bp_3));
  if (((*ap_6) == (*bp_3))) {
    
  } else {
    
  }
  if (((*ap_6) > (*bp_3))) {
    
  } else {
    
  }
  if (((*ap_6) < (*bp_3))) {
    
  } else {
    
  }
  if (((*ap_6) >= (*bp_3))) {
    
  } else {
    
  }
  if (((*ap_6) <= (*bp_3))) {
    
  } else {
    
  }
  if ((!((*ap_6) == (*bp_3)))) {
    
  } else {
    
  }
  if (((*cp_2) && (*dp_2))) {
    
  } else {
    
  }
  if (((*cp_2) || (*dp_2))) {
    
  } else {
    
  }
  if (((!(*cp_2)) || (*dp_2))) {
    
  } else {
    
  }
}

struct SPLArray* procReadLengthNew_1 () {
  struct SPLArray* a_33;
  struct SPLArray* tmp_5;
  int c_8;
  int b_22;
  
  tmp_5 = (struct SPLArray*) malloc(sizeof(struct SPLArray));
  tmp_5->length = 10;
  {
    for (int i = 0; i < 10; i++) {
      *((tmp_5->arr) + i) = (int*) malloc(sizeof(int));
    }
    
  }
  
  a_33 = tmp_5;
  b_22 = (a_33->length);
  *(((int**) (a_33->arr))[0]) = 1;
  c_8 = *(((int**) (a_33->arr))[0]);
  return a_33;
}

/*
 * Main Function, here for compilability
 */
int main() {
  return 0;
}
