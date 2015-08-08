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
struct SomeFields_1;

typedef struct SomeFields_1 {
  int x_1;
  bool y_1;
} SomeFields_1;

/*
 * Main Function, here for compilability
 */
int main() {
  return 0;
}
