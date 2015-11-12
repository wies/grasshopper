/*
 * Includes
 */
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>

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
int gclose (int fd);
int gopen (struct SPLArray* pathname, int flags);
int gread (int fd_2, struct SPLArray* buffer);
int greadOffset (int fd_3, struct SPLArray* buffer_1, int offset);
int gwrite (int fd_4, struct SPLArray* buffer_2);

int gclose (int fd){
  return close(fd);
}

int gopen (struct SPLArray* pathname, int flags){
  char* name = malloc(sizeof(char) * pathname->length);
  for (int i = 0; i < pathname->length; i++){
    name[i] = *((char*) pathname->arr[i]);
  }
  return open(name, flags);
}

int gread (int fd_2, struct SPLArray* buffer) {
  int* toRead = malloc(sizeof(int) * buffer->length);
  int res = read(fd_2, toRead, sizeof(int) * buffer->length);
  for (int i = 0; i < buffer->length; i++){
    buffer->arr[i] = (void *) toRead[i];
  }
  return res;
}

int gwrite (int fd_4, struct SPLArray* buffer_2){
  int* toWrite = malloc(sizeof(int) * buffer_2->length);
  for (int i = 0; i < buffer_2->length; i++){
    toWrite[i] =  (int) buffer_2->arr[i];
  }
  return write(fd_4, toWrite, buffer_2->length * sizeof(int));  
}

int greadOffset (int fd_3, struct SPLArray* buffer_1, int offset){
  int* toRead = malloc(sizeof(int) * buffer_1->length);
  int res = pread(fd_3, toRead, sizeof(int) * buffer_1->length, offset);
  for (int i = 0; i < buffer_1->length; i++){
    buffer_1->arr[i] = (void*) toRead[i];
  }
  return res;
}

/*
 * Main Function, here for compilability
 
int main() {
  return 0;
}
*/
