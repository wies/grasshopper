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
int checkPacket (SPLArray_char* packet);
SPLArray_char* constructPacket (SPLArray_char* req);
SPLArray_int* copy (SPLArray_int* a);
int gclose (int fd);
int gopen (SPLArray_char* pathname, int flags);
int gread (int fd_2, SPLArray_char* buffer);
int greadOffset (int fd_3, SPLArray_char* buffer_1, int offset);
int gwrite (int fd_4, SPLArray_char* buffer_2);
SPLArray_char* intToByteArray (int i_4);
void server (SPLArray_char* host);

int Main (SPLArray_char* args) {
  int res;
  server(args);
  res = 0;
  return res;
}

int checkPacket (SPLArray_char* packet) {
  int valid;
  char vt;
  char v;
  char mt;
  char m;
  char l;
  
  l = (((packet->arr[0]) & ((char) 255)) >> 6);
  vt = (((packet->arr[0]) & ((char) 255)) << 2);
  v = (vt >> 5);
  mt = (((packet->arr[0]) & ((char) 255)) << 5);
  m = (mt >> 5);
  valid = 0;
  if (((l == ((char) 0)) || (l == ((char) 3)))) {
    if (((v >= ((char) 1)) && (v <= ((char) 4)))) {
      if ((m == ((char) 3))) {
        valid = 1;
      }
    }
  }
  return valid;
}

SPLArray_char* constructPacket (SPLArray_char* req) {
  SPLArray_char* packet_1;
  SPLArray_char* tmp;
  char seconds;
  char fraction;
  
  tmp = newSPLArray_char( 12);
  packet_1 = tmp;
  seconds = ((char) 1);
  fraction = ((char) 1);
  (packet_1->arr[0]) = (((req->arr[0]) & ((char) 56)) + ((char) 1));
  (packet_1->arr[0]) = ((packet_1->arr[0]) + (((char) 1) << 8));
  (packet_1->arr[0]) = ((packet_1->arr[0]) + ((req->arr[0]) & (((char) 255) << 16)));
  (packet_1->arr[0]) = ((packet_1->arr[0]) + (((char) 236) << 24));
  (packet_1->arr[1]) = ((char) 0);
  (packet_1->arr[2]) = ((char) 0);
  (packet_1->arr[3]) = ((char) 1413695822);
  (packet_1->arr[4]) = seconds;
  (packet_1->arr[5]) = ((char) 0);
  (packet_1->arr[6]) = (req->arr[10]);
  (packet_1->arr[7]) = (req->arr[11]);
  (packet_1->arr[8]) = seconds;
  (packet_1->arr[9]) = fraction;
  (packet_1->arr[10]) = (req->arr[10]);
  (packet_1->arr[11]) = (req->arr[11]);
  return packet_1;
}

SPLArray_int* copy (SPLArray_int* a) {
  SPLArray_int* b;
  SPLArray_int* tmp_1;
  int i_1;
  
  tmp_1 = newSPLArray_int( (a->length));
  b = tmp_1;
  i_1 = 0;
  while (true) {
    if (!((i_1 < (a->length)))) {
      break;
    }
    (b->arr[i_1]) = (a->arr[i_1]);
    i_1 = (i_1 + 1);
  }
  return b;
}

SPLArray_char* intToByteArray (int i_4) {
  SPLArray_char* arr;
  SPLArray_char* tmp_2;
  
  tmp_2 = newSPLArray_char( 4);
  arr = tmp_2;
  (arr->arr[0]) = ((char) (i_4 >> 0));
  (arr->arr[1]) = ((char) (i_4 >> 8));
  (arr->arr[2]) = ((char) (i_4 >> 16));
  (arr->arr[3]) = ((char) (i_4 >> 24));
  return arr;
}

void server (SPLArray_char* host) {
  SPLArray_char* tmp_5;
  int tmp_4;
  SPLArray_char* tmp_3;
  int temp;
  int flags_1;
  int fd_5;
  SPLArray_char* buffer_3;
  
  flags_1 = 0;
  fd_5 = gopen(host, flags_1);
  tmp_3 = newSPLArray_char( 12);
  buffer_3 = tmp_3;
  temp = gread(fd_5, buffer_3);
  tmp_4 = checkPacket(buffer_3);
  if ((!(tmp_4 == 0))) {
    tmp_5 = constructPacket(buffer_3);
    temp = gwrite(fd_5, tmp_5);
  }
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

