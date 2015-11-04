#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdlib.h>
#include "fileio.h"
#include <stdio.h>
#include <errno.h>
#include <string.h>

//Jenny Ramseyer

//TODO: Add create.

int gclose (int fd){
  return close(fd);
}

//put the filename you want to open in arr[0]
//make sure you allocate enough space.
int gopen (struct SPLArray* pathname, int flags){
  char * name;
  name = pathname->arr[0];
  return open(name, flags);
}

//will read into arr[0]
int gread (int fd_2, struct SPLArray* buffer) {
  return read(fd_2, buffer->arr[0], buffer->length);
}

//put what you want to write in arr[0]
//make sure you specify length in length
int gwrite (int fd_3, struct SPLArray* buffer_1){
  return write(fd_3, buffer_1->arr[0], buffer_1->length);  
}


int main() {
  /* 
  struct SPLArray* test = malloc( sizeof( struct SPLArray) + 5);
  test->length = 5;
  test->arr[0] = "t.txt";

  int fd = gopen(test, O_RDWR);

  if (fd < 0){
    printf("Can't open: %s\n", strerror(errno));
  }

  struct SPLArray* writeme = malloc(sizeof(struct SPLArray) + 5);
  writeme->length = 5;
  writeme->arr[0] = "hello";

  int suc = gwrite(fd, writeme);
  if (suc < 0){
    printf("Did not write: %s\n", strerror(errno));
  }

  struct SPLArray* readtome = malloc(sizeof(struct SPLArray) + 5);
  readtome->length = 5;
  readtome->arr[0] = malloc(sizeof(char) * (readtome->length));

  suc = gread(fd, readtome);
  printf("number of bytes read: %d\n", suc);
  if (suc < 0){
    printf("Did not read: %s\n", strerror(errno));
  }
  printf("We read: %s\n", readtome->arr[0]);
  suc = gclose(fd);
  if (suc < 0) {
      printf("Did not close: %s\n", strerror(errno));
  }
  free(readtome);
  free(test);
  free(writeme);
*/  return 0;
}

