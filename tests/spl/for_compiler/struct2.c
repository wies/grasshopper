/*
 * Includes
 */
#include <stdbool.h>

/*
 * Preloaded Code
 */
typedef struct SPLArray {
  int length;
  void* arr[];
} SPLArray;


/*
 * Structs
 */
struct RecStruct_1;

typedef struct RecStruct_1 {
  int data_1;
  struct RecStruct_1* next_1;
} RecStruct_1;