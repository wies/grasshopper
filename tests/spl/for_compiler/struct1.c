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
struct SomeFields0_1;
struct SomeFields1_1;
struct SomeFields2_1;
struct SomeFields3_1;
struct SomeFields4_1;

typedef struct SomeFields0_1 {
  int x0_1;
  bool y0_1;
} SomeFields0_1;

typedef struct SomeFields1_1 {
  int x1_1;
  bool y1_1;
} SomeFields1_1;

typedef struct SomeFields2_1 {
  int x2_1;
  bool y2_1;
} SomeFields2_1;

typedef struct SomeFields3_1 {
  int x3_1;
  bool y3_1;
} SomeFields3_1;

typedef struct SomeFields4_1 {
  int x4_1;
  bool y4_1;
} SomeFields4_1;

int main() {return 0;}
