/*
 * Includes
 */
#include <stdbool.h>
#include <stdlib.h>
#include "fileIO.h"

/*
 * Preloaded Code
 
typedef struct SPLArray {
  int length;
  void* arr[];
} SPLArray;

void freeSPLArray (SPLArray* a) {
  free(a->arr);
  free(a);
}
*/

/*
 * Procedures
 */
int checkPacket (struct SPLArray* packet);
struct SPLArray* constructPacket (struct SPLArray* req);
struct SPLArray* copy (struct SPLArray* a);
//int gclose (int fd);
//int gopen (struct SPLArray* pathname, int flags);
//int gread (int fd_2, struct SPLArray* buffer);
//int greadOffset (int fd_3, struct SPLArray* buffer_1, int offset);
//int gwrite (int fd_4, struct SPLArray* buffer_2);
struct SPLArray* intToByteArray (int i_4);
void server (struct SPLArray* host);

int checkPacket (struct SPLArray* packet) {
  int valid;
  int v;
  int m;
  int l;
  
  l = (((((int*) (packet->arr))[0]) & 255) >> 6);
  v = ((((((int*) (packet->arr))[0]) & 255) << 2) >> 5);
  m = ((((((int*) (packet->arr))[0]) & 255) << 5) >> 5);
  valid = 0;
  printf("l %x v %x m %x\n", l, v, m);
  if (((l == 0) || (l == 3))) {
    if (((v >= 1) && (v <= 4))) {
      if ((m == 3)) {
        valid = 1;
      }
    }
  }
  return valid;
}

struct SPLArray* constructPacket (struct SPLArray* req) {
  struct SPLArray* packet_1;
  struct SPLArray* tmp;
  int seconds;
  int fraction;
  
  tmp = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 12));
  tmp->length = 12;
  {
    for (int i = 0; i < 12; i++) {
      (tmp->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  packet_1 = tmp;
  seconds = 1;
  fraction = 1;
  (((int*) (packet_1->arr))[0]) = (((((int*) (req->arr))[0]) & 56) + 1);
  (((int*) (packet_1->arr))[0]) = ((((int*) (packet_1->arr))[0]) + (1 << 8));
  (((int*) (packet_1->arr))[0]) = ((((int*) (packet_1->arr))[0]) + ((((int*) (req->arr))[0]) & (255 << 16)));
  (((int*) (packet_1->arr))[0]) = ((((int*) (packet_1->arr))[0]) + (236 << 24));
  (((int*) (packet_1->arr))[1]) = 0;
  (((int*) (packet_1->arr))[2]) = 0;
  (((int*) (packet_1->arr))[3]) = 1413695822;
  (((int*) (packet_1->arr))[4]) = seconds;
  (((int*) (packet_1->arr))[5]) = 0;
  (((int*) (packet_1->arr))[6]) = (((int*) (req->arr))[10]);
  (((int*) (packet_1->arr))[7]) = (((int*) (req->arr))[11]);
  (((int*) (packet_1->arr))[8]) = seconds;
  (((int*) (packet_1->arr))[9]) = fraction;
  (((int*) (packet_1->arr))[10]) = (((int*) (req->arr))[10]);
  (((int*) (packet_1->arr))[11]) = (((int*) (req->arr))[11]);
  return packet_1;
}

struct SPLArray* copy (struct SPLArray* a) {
  struct SPLArray* b;
  struct SPLArray* tmp_1;
  int i_1;
  
  tmp_1 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * (a->length)));
  tmp_1->length = (a->length);
  {
    for (int i = 0; i < (a->length); i++) {
      (tmp_1->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  b = tmp_1;
  i_1 = 0;
  while (true) {
    if (!((i_1 < (a->length)))) {
      break;
    }
    *(((int**) (b->arr))[i_1]) = *(((int**) (a->arr))[i_1]);
    i_1 = (i_1 + 1);
  }
  return b;
}

struct SPLArray* intToByteArray (int i_4) {
  struct SPLArray* arr;
  struct SPLArray* tmp_2;
  
  tmp_2 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 4));
  tmp_2->length = 4;
  {
    for (int i = 0; i < 4; i++) {
      (tmp_2->arr)[i] = (char*) malloc(sizeof(char));
    }
    
  }
  arr = tmp_2;
  *(((char**) (arr->arr))[0]) = ((char) (i_4 >> 0));
  *(((char**) (arr->arr))[1]) = ((char) (i_4 >> 8));
  *(((char**) (arr->arr))[2]) = ((char) (i_4 >> 16));
  *(((char**) (arr->arr))[3]) = ((char) (i_4 >> 24));
  return arr;
}

void server (struct SPLArray* host) {
  struct SPLArray* tmp_5;
  int tmp_4;
  struct SPLArray* tmp_3;
  int temp;
  int flags_1;
  int fd_5;
  struct SPLArray* buffer_3;
  
  flags_1 = O_RDWR;
  fd_5 = gopen(host, flags_1);
  tmp_3 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 12));
  tmp_3->length = 12;
  {
    for (int i = 0; i < 12; i++) {
      (tmp_3->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  buffer_3 = tmp_3;
  temp = gread(fd_5, buffer_3);
  tmp_4 = checkPacket(buffer_3);
  printf("tmp_4 is %d\n", tmp_4);
  if ((!(tmp_4 == 0))) {
    tmp_5 = constructPacket(buffer_3);
    temp = gwrite(fd_5, tmp_5);
  }
}

/*
 * Main Function, here for compilability
 */
int main() {
  struct SPLArray* host;
  host = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 5));
  host->length = 5;
  for (int i = 0; i < 5; i++){
    (host->arr)[i] = (char*) malloc(sizeof(char));
  }
  *(((char**) (host->arr))[0]) = 'p';
  *(((char**) (host->arr))[1]) = '.';
  *(((char**) (host->arr))[2]) = 't';
  *(((char**) (host->arr))[3]) = 'x';
  *(((char**) (host->arr))[4]) = 't';

  server(host);

  return 0;
}
