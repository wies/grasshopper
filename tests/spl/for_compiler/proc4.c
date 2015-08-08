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
struct Node_1;
struct NodeBlack_1;
struct NodeWhite_1;

typedef struct Node_1 {
  int data_1;
  struct Node_1* next_5;
} Node_1;

typedef struct NodeBlack_1 {
  bool bool_6;
  int number_5;
  struct SPLArray* someMoreNumbers_5;
  struct NodeWhite_1* white_5;
} NodeBlack_1;

typedef struct NodeWhite_1 {
  struct NodeBlack_1* black_5;
} NodeWhite_1;

/*
 * Procedures
 */
struct NodeBlack_1* blackAndWhiteChain_1 (int n_12);
void clearNodeBlackChain_1 (struct NodeBlack_1* h_17);
struct Node_1* emptyChain_1 (int n_13);
void freeChain_1 (struct Node_1* head_11);
struct NodeBlack_1* helperBlack_1 (int n_14);
struct NodeWhite_1* helperWhite_1 (int n_15);

struct NodeBlack_1* blackAndWhiteChain_1 (int n_12) {
  struct NodeBlack_1* h_16;
  h_16 = helperBlack_1(n_12);
  return h_16;
  return h_16;
}

void clearNodeBlackChain_1 (struct NodeBlack_1* h_17) {
  struct NodeWhite_1* whiteN_7;
  bool curIsBlack_8;
  struct NodeBlack_1* blackN_7;
  
  blackN_7 = h_17;
  
  curIsBlack_8 = true;
  while (true) {
    if (!(((!(blackN_7 == NULL)) || (!(whiteN_7 == NULL))))) {
      break;
    }
    if (curIsBlack_8) {
      whiteN_7 = (blackN_7->white_5);
      free(blackN_7);
      
      curIsBlack_8 = false;
    } else {
      blackN_7 = (whiteN_7->black_5);
      free(whiteN_7);
      
      curIsBlack_8 = true;
    }
  }
}

struct Node_1* emptyChain_1 (int n_13) {
  struct Node_1* head_10;
  struct Node_1* tmp_25;
  struct Node_1* tmp_24;
  int i_14;
  struct Node_1* cur_7;
  
  if ((n_13 <= 0)) {
    return NULL;
  }
  tmp_24 = ((struct Node_1*) malloc(sizeof(struct Node_1)));
  head_10 = tmp_24;
  cur_7 = head_10;
  i_14 = 0;
  while (true) {
    if (!((i_14 < (n_13 - 1)))) {
      break;
    }
    tmp_25 = ((struct Node_1*) malloc(sizeof(struct Node_1)));
    (cur_7->next_5) = tmp_25;
    cur_7 = (cur_7->next_5);
    i_14 = (i_14 + 1);
  }
  (cur_7->next_5) = NULL;
  return head_10;
}

void freeChain_1 (struct Node_1* head_11) {
  struct Node_1* temp_7;
  
  
  while (true) {
    if (!((!(head_11 == NULL)))) {
      break;
    }
    temp_7 = head_11;
    head_11 = (head_11->next_5);
    free(temp_7);
    
  }
}

struct NodeBlack_1* helperBlack_1 (int n_14) {
  struct NodeBlack_1* h_18;
  struct NodeWhite_1* tmp_29;
  struct SPLArray* tmp_28;
  struct SPLArray* tmp_27;
  struct NodeBlack_1* tmp_26;
  int i_15;
  
  if ((n_14 <= 0)) {
    return NULL;
  } else {
    tmp_26 = ((struct NodeBlack_1*) malloc(sizeof(struct NodeBlack_1)));
    h_18 = tmp_26;
    (h_18->number_5) = n_14;
    if ((n_14 <= 6)) {
      (h_18->bool_6) = false;
    } else {
      (h_18->bool_6) = true;
    }
    tmp_27 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * n_14));
    tmp_27->length = n_14;
    {
      for (int i = 0; i < n_14; i++) {
        (tmp_27->arr)[i] = (int*) malloc(sizeof(int));
      }
      
    }
    
    (h_18->someMoreNumbers_5) = tmp_27;
    i_15 = 0;
    while (true) {
      if (!((i_15 < n_14))) {
        break;
      }
      tmp_28 = (h_18->someMoreNumbers_5);
      *(((int**) (tmp_28->arr))[i_15]) = (i_15 * i_15);
      i_15 = (i_15 + 1);
    }
    tmp_29 = helperWhite_1((n_14 - 1));
    (h_18->white_5) = tmp_29;
    return h_18;
  }
  return h_18;
}

struct NodeWhite_1* helperWhite_1 (int n_15) {
  struct NodeWhite_1* h_19;
  struct NodeBlack_1* tmp_31;
  struct NodeWhite_1* tmp_30;
  
  if ((n_15 <= 0)) {
    return NULL;
  } else {
    tmp_30 = ((struct NodeWhite_1*) malloc(sizeof(struct NodeWhite_1)));
    h_19 = tmp_30;
    tmp_31 = helperBlack_1((n_15 - 1));
    (h_19->black_5) = tmp_31;
    return h_19;
  }
  return h_19;
}

/*
 * Main Function, here for compilability
 */
int main() {
  return 0;
}
