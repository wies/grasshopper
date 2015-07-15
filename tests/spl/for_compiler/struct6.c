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
struct First_1;
struct Second_1;

typedef struct First_1 {
  struct First_1* a_1;
  struct Second_1* b_1;
  int c_1;
} First_1;

typedef struct Second_1 {
  struct First_1* e_1;
  struct Second_1* f_1;
  int g_1;
} Second_1;

int main() {return 0;}
