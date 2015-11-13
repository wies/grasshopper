#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdlib.h>
#include "fileio.h"
#include <stdio.h>
#include <errno.h>
#include <string.h>

//Jenny Ramseyer


int gclose (int fd){
  return close(fd);
}

int gopen (SPLArray_char* pathname, int flags){
  //check if null terminated
  bool null_terminated = false;
  for(int i = 0; i < pathname->length && !null_terminated; i++) {
    null_terminated |= (pathname->arr[i] == 0);
  }
  if (null_terminated) {
    //valid C string
    return open(pathname->arr, flags);
  } else {
    //create a valid C string
    char name[pathname->length + 1]; //allocate on the stack for simplicity
    for(int i = 0; i < pathname->length; i++) {
      name[i] = pathname->arr[i];
    }
    name[pathname->length] = 0;
    return open(name, flags);
  }
}

int gread (int fd_2, SPLArray_char* buffer) {
  return read(fd_2, buffer->arr, buffer->length);
}

int gwrite (int fd_4, SPLArray_char* buffer_2){
  return write(fd_4, buffer_2->arr, buffer_2->length);  
}

int greadOffset (int fd_3, SPLArray_char* buffer_1, int offset){
  return pread(fd_3, buffer_1->arr, buffer_1->length, offset);
}

//int main() {
  /*
  SPLArray_char* test;
  test = (SPLArray_char*) malloc(sizeof(SPLArray_char) + (sizeof(char) * 6));
  test->length = 5;
  test->arr[0] = 't';
  test->arr[1] = '.';
  test->arr[2] = 't';
  test->arr[3] = 'x';
  test->arr[4] = 't';
  test->arr[5] = 0; //C string are terminated by 0.

  int fd = gopen(test, O_RDWR);

  if (fd < 0){
    printf("Can't open: %s\n", strerror(errno));
    return -1;
  }

  SPLArray_char* writeMe;
  writeMe = (SPLArray_char*) malloc(sizeof(SPLArray_char) + (sizeof(char) * 5));
  writeMe->length = 5;
  writeMe->arr[0] = 'h';
  writeMe->arr[1] = 'e';
  writeMe->arr[2] = 'l';
  writeMe->arr[3] = 'l';
  writeMe->arr[4] = 'o';

  int suc = gwrite(fd, writeMe);
  if (suc < 0){
    printf("Did not write: %s\n", strerror(errno));
    return -1;
  }

  SPLArray_char* readToMe;
  readToMe = (SPLArray_char*) malloc(sizeof(SPLArray_char) + (sizeof(char) * 5));
  readToMe->length = 5;

  gclose(fd);
  fd = gopen(test, O_RDWR);

  suc = gread(fd, readToMe);
  printf("number of bytes read: %d\n", suc);
  if (suc < 0){
    printf("Did not read: %s\n", strerror(errno));
    return -1;
  }
  printf("We read: %c%c%c%c%c\n", 
	 readToMe->arr[0], 
	 readToMe->arr[1], 
	 readToMe->arr[2], 
	 readToMe->arr[3], 
	 readToMe->arr[4]);

  SPLArray_char* readOffset;
  readOffset = (SPLArray_char*) malloc(sizeof(SPLArray_char) + (sizeof(char) * 10));
  readOffset->length = 10;
  suc = greadOffset(fd, readOffset, 0);
  printf("number of bytes read: %d\n", suc);
  if (suc < 0){
    printf("Did not read with offset: %s\n", strerror(errno));
  }
  printf("We read: %c%c%c%c%c%c%c%c%c%c\n",
	 readOffset->arr[0],
	 readOffset->arr[1],
	 readOffset->arr[2],
	 readOffset->arr[3],
	 readOffset->arr[4],
	 readOffset->arr[5],
	 readOffset->arr[6],
	 readOffset->arr[7],
	 readOffset->arr[8], 
	 readOffset->arr[9]);

  suc = gclose(fd);
  if (suc < 0) {
      printf("Did not close: %s\n", strerror(errno));
  }
  free(readToMe);
  free(test);
  free(writeMe);
  free(readOffset);
  *///  return 0;
//}

