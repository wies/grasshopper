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
struct RecStruct_1;

typedef struct RecStruct_1 {
  int data_1;
  struct RecStruct_1* next_1;
} RecStruct_1;

/*
 * Main Function, here for compilability
 */
int main() {
  return 0;
}
