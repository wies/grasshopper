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
struct SPLArray* copy_1 (struct SPLArray* a_26);

void procCall_1 (int* a_27, bool* b_17);

void procIntAndBoolVal_1 (int* a_28, bool* b_18);

int procNull_1 ();

void procOps_1 (int a_30, int b_19, bool c_5, bool d_1, int* ap_6, int* bp_3, bool* cp_2, bool* dp_2);

struct SPLArray* copy_1 (struct SPLArray* a_26) {
  struct SPLArray* b_16;
  tmp_2 = (struct SPLArray*) malloc(sizeof(struct SPLArray));
  tmp_2->length = (a_26->length);
  {
    for (int i = 0; i < (a_26->length); i++) {
      *((tmp_2->arr) + i) = (int*) malloc(sizeof(int))
    }
    
  }
  
  b_16 = tmp_2;
  i_27 = 0;
  while (true) {
    
    if (!(i_27 < (a_26->length))) {
      break;
    }
    *(((int**) (b_16->arr))[i_27]) = *(((int**) (a_26->arr))[i_27]);
    i_27 = i_27 + 1;
  }
  return b_16;
}

void procCall_1 (int* a_27, bool* b_17) {
  procIntAndBoolVal_1(&(*a_27), &(*b_17));
  *a_27 = (*a_27);
  *b_17 = (*b_17);
  return;
}

void procIntAndBoolVal_1 (int* a_28, bool* b_18) {
  (*a_28) = 1;
  (*a_28) = -1;
  (*a_28) = 0;
  (*a_28) = 277;
  (*b_18) = true;
  (*b_18) = false;
}

int procNull_1 () {
  int a_29;
  if (NULL == NULL) {
    a_29 = 1;
  } else {
    a_29 = 0;
  }
  return a_29;
}

void procOps_1 (int a_30, int b_19, bool c_5, bool d_1, int* ap_6, int* bp_3, bool* cp_2, bool* dp_2) {
  (*ap_6) = a_30;
  (*bp_3) = b_19;
  (*cp_2) = c_5;
  (*dp_2) = d_1;
  (*ap_6) = -(*ap_6);
  if (!(*dp_2)) {
    
  } else {
    
  }
  (*ap_6) = (*ap_6) + (*bp_3);
  (*bp_3) = (*ap_6) - (*bp_3);
  (*ap_6) = (*ap_6) * (*bp_3);
  (*ap_6) = (*ap_6) / (*bp_3);
  if ((*ap_6) == (*bp_3)) {
    
  } else {
    
  }
  if ((*ap_6) > (*bp_3)) {
    
  } else {
    
  }
  if ((*ap_6) < (*bp_3)) {
    
  } else {
    
  }
  if ((*ap_6) >= (*bp_3)) {
    
  } else {
    
  }
  if ((*ap_6) <= (*bp_3)) {
    
  } else {
    
  }
  if (!(*ap_6) == (*bp_3)) {
    
  } else {
    
  }
  if ((*cp_2) && (*dp_2)) {
    
  } else {
    
  }
  if ((*cp_2) || (*dp_2)) {
    
  } else {
    
  }
  if (((!(*cp_2)) || (*dp_2))) {
    
  } else {
    
  }
}

int main() {
  return 0;
}
