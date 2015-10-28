#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdlib.h>
#include "fileio.c"

void gclose (int fd){
  close(fd);
}

int gopen (struct SPLArray* pathname, int flags){
  return open((char *) pathname->arr, flags);
}

int gread (int fd_2, struct SPLArray* buffer) {
  return read(fd_2, buffer, sizeof(buffer));
}

int gwrite (int fd_3, struct SPLArray* buffer_1){
  return write(fd_3, buffer_1, sizeof(buffer_1));  
}

