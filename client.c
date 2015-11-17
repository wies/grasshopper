/*
 * Includes
 */
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>

/*
 * Preloaded Code
 */

typedef struct {
  int length;
  int arr[];
} SPLArray_int;

SPLArray_int* newSPLArray_int(int size) {
  SPLArray_int* a = (SPLArray_int*)malloc(sizeof(SPLArray_int) + size * sizeof(int));
  assert(a != NULL);
  a->length = size;
  return a;
}

typedef struct {
  int length;
  bool arr[];
} SPLArray_bool;

SPLArray_bool* newSPLArray_bool(int size) {
  SPLArray_bool* a = (SPLArray_bool*)malloc(sizeof(SPLArray_bool) + size * sizeof(bool));
  assert(a != NULL);
  a->length = size;
  return a;
}

typedef struct {
  int length;
  char arr[];
} SPLArray_char;

SPLArray_char* newSPLArray_char(int size) {
  SPLArray_char* a = (SPLArray_char*)malloc(sizeof(SPLArray_char) + size * sizeof(char));
  assert(a != NULL);
  a->length = size;
  return a;
}

typedef struct {
  int length;
  void* arr[];
} SPLArray_generic;

SPLArray_generic* newSPLArray_generic(int size) {
  SPLArray_generic* a = (SPLArray_generic*)malloc(sizeof(SPLArray_generic) + size * sizeof(void*));
  assert(a != NULL);
  a->length = size;
  return a;
}


/*
 * Procedures
 */
int Main (SPLArray_char* args);
int client (SPLArray_char* host, int mode, int version);
SPLArray_char* constructPacket (int mode_1, int version_1);
SPLArray_int* copy (SPLArray_int* a);
SPLArray_char* copyByte (SPLArray_char* a_1);
int gclose (int fd_1);
int gopen (SPLArray_char* pathname, int flags_1);
int gread (int fd_3, SPLArray_char* buffer_1);
int greadOffset (int fd_4, SPLArray_char* buffer_2, int offset);
int gwrite (int fd_5, SPLArray_char* buffer_3);
SPLArray_char* intToByteArray (int i_8);

int Main (SPLArray_char* args) {
  int res;
  res = client(args, 1, 1);
  return res;
}

int client (SPLArray_char* host, int mode, int version) {
  int time;
  int temp;
  SPLArray_char* packet;
  int flags;
  int fd;
  SPLArray_char* buffer;
  
  flags = 0;
  fd = gopen(host, flags);
  packet = constructPacket(mode, version);
  buffer = copyByte(packet);
  temp = gwrite(fd, buffer);
  temp = greadOffset(fd, buffer, 0);
  return ((int) (((buffer->arr[9]) * ((char) 1000000000)) + ((buffer->arr[10]) * (((char) 1000000000) >> 32))));
}

SPLArray_char* constructPacket (int mode_1, int version_1) {
  SPLArray_char* packet_1;
  SPLArray_char* tmp;
  int i_1;
  
  tmp = newSPLArray_char( 12);
  packet_1 = tmp;
  i_1 = 0;
  while (true) {
    if (!((i_1 < (packet_1->length)))) {
      break;
    }
    (packet_1->arr[i_1]) = ((char) 0);
    i_1 = (i_1 + 1);
  }
  (packet_1->arr[0]) = (((packet_1->arr[0]) & ((char) 199)) | ((char) mode_1));
  (packet_1->arr[0]) = (((packet_1->arr[0]) & ((char) 199)) | (((char) version_1) << 3));
  return packet_1;
}

SPLArray_int* copy (SPLArray_int* a) {
  SPLArray_int* b;
  SPLArray_int* tmp_1;
  int i_3;
  
  tmp_1 = newSPLArray_int( (a->length));
  b = tmp_1;
  i_3 = 0;
  while (true) {
    if (!((i_3 < (a->length)))) {
      break;
    }
    (b->arr[i_3]) = (a->arr[i_3]);
    i_3 = (i_3 + 1);
  }
  return b;
}

SPLArray_char* copyByte (SPLArray_char* a_1) {
  SPLArray_char* b_1;
  SPLArray_char* tmp_2;
  int i_5;
  
  tmp_2 = newSPLArray_char( (a_1->length));
  b_1 = tmp_2;
  i_5 = 0;
  while (true) {
    if (!((i_5 < (a_1->length)))) {
      break;
    }
    (b_1->arr[i_5]) = (a_1->arr[i_5]);
    i_5 = (i_5 + 1);
  }
  return b_1;
}

SPLArray_char* intToByteArray (int i_8) {
  SPLArray_char* arr;
  SPLArray_char* tmp_3;
  
  tmp_3 = newSPLArray_char( 4);
  arr = tmp_3;
  (arr->arr[0]) = ((char) (i_8 >> 0));
  (arr->arr[1]) = ((char) (i_8 >> 8));
  (arr->arr[2]) = ((char) (i_8 >> 16));
  (arr->arr[3]) = ((char) (i_8 >> 24));
  return arr;
}

/*
 * Main Function, here for compilability
 */
int main(int argc, char *argv[]) {
  assert(argc <= 2);
  int s = 0;
  if (argc > 1) {
    for(s = 0; argv[1][s] != 0; s++) { }
    s++;
  }
  SPLArray_char* a = newSPLArray_char(s);
  for(int i = 0; i < s; i++) {
    a->arr[i] = argv[1][i];
  }
  return Main(a);
}

