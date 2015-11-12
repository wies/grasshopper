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

int gopen (struct SPLArray* pathname, int flags){
  char* name = malloc(sizeof(char) * pathname->length);
  for (int i = 0; i < pathname->length; i++){
    name[i] = *((char*) pathname->arr[i]);
  }
  return open(name, flags);
}

int gread (int fd_2, struct SPLArray* buffer) {
  char* toRead = malloc(sizeof(char) * buffer->length);
  int res = read(fd_2, toRead, buffer->length);
  for (int i = 0; i < buffer->length; i++){
    buffer->arr[i] = (void *) toRead[i];
  }
  return res;
}

int gwrite (int fd_4, struct SPLArray* buffer_2){
  char* toWrite = malloc(sizeof(char) * buffer_2->length);
  for (int i = 0; i < buffer_2->length; i++){
    toWrite[i] = *((char*) buffer_2->arr[i]);
  }
  return write(fd_4, toWrite, buffer_2->length);  
}

int greadOffset (int fd_3, struct SPLArray* buffer_1, int offset){
  char* toRead = malloc(sizeof(char) * buffer_1->length);
  int res = pread(fd_3, toRead, buffer_1->length, offset);
  for (int i = 0; i < buffer_1->length; i++){
    buffer_1->arr[i] = (void*) toRead[i];
  }
  return res;
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

