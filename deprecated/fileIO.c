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
  struct SPLArray* test;
  test = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 5));
  test->length = 5;
  for (int i = 0; i < 5; i++){
    (test->arr)[i] = (char*) malloc(sizeof(char));
  }
  *(((char**) (test->arr))[0]) = 't';
  *(((char**) (test->arr))[1]) = '.';
  *(((char**) (test->arr))[2]) = 't';
  *(((char**) (test->arr))[3]) = 'x';
  *(((char**) (test->arr))[4]) = 't';

  int fd = gopen(test, O_RDWR);

  if (fd < 0){
    printf("Can't open: %s\n", strerror(errno));
  }

  struct SPLArray* writeMe;
  writeMe = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 5));
  writeMe->length = 5;
  for (int i = 0; i < 5; i++){
    (writeMe->arr)[i] = (char*) malloc(sizeof(char));
  }
  *(((char**) (writeMe->arr))[0]) = 'h';
  *(((char**) (writeMe->arr))[1]) = 'e';
  *(((char**) (writeMe->arr))[2]) = 'l';
  *(((char**) (writeMe->arr))[3]) = 'l';
  *(((char**) (writeMe->arr))[4]) = 'o';

  int suc = gwrite(fd, writeMe);
  if (suc < 0){
    printf("Did not write: %s\n", strerror(errno));
  }

  struct SPLArray* readToMe;
  readToMe = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 5));
  readToMe->length = 5;
  for (int i = 0; i < 5; i++){
    (readToMe->arr)[i] = (char*) malloc(sizeof(char));
  }

  suc = gread(fd, readToMe);
  printf("number of bytes read: %d\n", suc);
  if (suc < 0){
    printf("Did not read: %s\n", strerror(errno));
  }
  printf("We read: %c%c%c%c%c\n", 
	 (char*) readToMe->arr[0], 
	 (char*) readToMe->arr[1], 
	 (char*) readToMe->arr[2], 
	 (char*) readToMe->arr[3], 
	 (char*) readToMe->arr[4]);

  struct SPLArray* readOffset;
  readOffset = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 10));
  readOffset->length = 10;
  for (int i = 0; i < 10; i ++){
    (readOffset->arr)[i] = (char*) malloc(sizeof(char));
  }
  suc = greadOffset(fd, readOffset, 0);
  printf("number of bytes read: %d\n", suc);
  if (suc < 0){
    printf("Did not read with offset: %s\n", strerror(errno));
  }
  printf("We read: %c%c%c%c%c%c%c%c%c%c\n",
	 (char*) readOffset->arr[0],
	 (char*) readOffset->arr[1],
	 (char*) readOffset->arr[2],
	 (char*) readOffset->arr[3],
	 (char*) readOffset->arr[4],
	 (char*) readOffset->arr[5],
	 (char*) readOffset->arr[6],
	 (char*) readOffset->arr[7],
	 (char*) readOffset->arr[8], 
	 (char*) readOffset->arr[9]);

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

