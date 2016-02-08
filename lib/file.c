#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdlib.h>
#include "file.h"
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <sys/stat.h>



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
    if ((flags & O_CREAT) != 0) {
        return open(pathname->arr, flags, S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
    } else {
        return open(pathname->arr, flags);
    }
  } else {
    //create a valid C string
    char name[pathname->length + 1]; //allocate on the stack for simplicity
    for(int i = 0; i < pathname->length; i++) {
      name[i] = pathname->arr[i];
    }
    name[pathname->length] = 0;
    if ((flags & O_CREAT) != 0) {
        return open(name, flags, S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
    } else {
        return open(name, flags);
    }
  }
}

int gread (int fd_2, SPLArray_char* buffer) {
  return read(fd_2, buffer->arr, buffer->length);
}

int gwrite (int fd_4, SPLArray_char* buffer_2){
  return write(fd_4, buffer_2->arr, buffer_2->length);  
}

int gwrite2 (int fd_4, SPLArray_char* buffer_2, int size){
  return write(fd_4, buffer_2->arr, size);  
}

int greadOffset (int fd_3, SPLArray_char* buffer_1, int offset){
  return pread(fd_3, buffer_1->arr, buffer_1->length, offset);
}

int fileSize(SPLArray_char* pathname) {
  struct stat st;
  bool null_terminated = false;
  for(int i = 0; i < pathname->length && !null_terminated; i++) {
    null_terminated = (pathname->arr[i] == 0);
  }

  if (null_terminated) {
    if (stat(pathname->arr, &st) == 0) {
      return (int)st.st_size;
    }
  } else {
    char name[pathname->length + 1]; //allocate on the stack for simplicity
    memcpy(name, pathname->arr, pathname->length);
    name[pathname->length] = 0;
    if (stat(name, &st) == 0) {
      return (int)st.st_size;
    }
  }
  return -1; 
}
