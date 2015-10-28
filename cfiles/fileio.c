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
void gclose (int fd);
int gopen (struct SPLArray* pathname, int flags);
int gread (int fd_2, struct SPLArray* buffer);
int gwrite (int fd_3, struct SPLArray* buffer_1);



/*
 * Main Function, here for compilability
 */
int main() {
  return 0;
}
