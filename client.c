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
int client (struct SPLArray* host, int mode, int version);
struct SPLArray* constructPacket (int mode_1, int version_1);
struct SPLArray* copy (struct SPLArray* a);
//int gclose (int fd_1);
//int gopen (struct SPLArray* pathname, int flags_1);
//int gread (int fd_3, struct SPLArray* buffer_1);
//int greadOffset (int fd_4, struct SPLArray* buffer_2, int offset);
//int gwrite (int fd_5, struct SPLArray* buffer_3);
struct SPLArray* intToByteArray (int i_6);

int client (struct SPLArray* host, int mode, int version) {
  int time;
  int temp;
  struct SPLArray* packet;
  int flags;
  int fd;
  struct SPLArray* buffer;
  
  flags = O_RDWR;
  fd = gopen(host, flags);
  packet = constructPacket(mode, version);
  buffer = copy(packet);
  temp = gwrite(fd, buffer);
  //temp = greadOffset(fd, buffer, 0);
  //return ((*(((int**) (buffer->arr))[9]) * 1000000000) + (*(((int**) (buffer->arr))[10]) * (1000000000 >> 32)));
  return 0;
}

struct SPLArray* constructPacket (int mode_1, int version_1) {
  struct SPLArray* packet_1;
  struct SPLArray* tmp;
  int i_1;
  
  tmp = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * 12));
  tmp->length = 12;
  {
    for (int i = 0; i < 12; i++) {
      (tmp->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  packet_1 = tmp;
  i_1 = 0;
  while (true) {
    if (!((i_1 < (packet_1->length)))) {
      break;
    }
    *(((int**) (packet_1->arr))[i_1]) = 0;
    i_1 = (i_1 + 1);
  }
  *(((int**) (packet_1->arr))[0]) = ((*(((int**) (packet_1->arr))[0]) & 199) | mode_1);
  *(((int**) (packet_1->arr))[0]) = ((*(((int**) (packet_1->arr))[0]) & 199) | (version_1 << 3));
  return packet_1;
}

struct SPLArray* copy (struct SPLArray* a) {
  struct SPLArray* b;
  struct SPLArray* tmp_1;
  int i_3;
  
  tmp_1 = (struct SPLArray*) malloc(sizeof(struct SPLArray) + (sizeof(void*) * (a->length)));
  tmp_1->length = (a->length);
  {
    for (int i = 0; i < (a->length); i++) {
      (tmp_1->arr)[i] = (int*) malloc(sizeof(int));
    }
    
  }
  b = tmp_1;
  i_3 = 0;
  while (true) {
    if (!((i_3 < (a->length)))) {
      break;
    }
    *(((int**) (b->arr))[i_3]) = *(((int**) (a->arr))[i_3]);
    i_3 = (i_3 + 1);
  }
  return b;
}

struct SPLArray* intToByteArray (int i_6) {
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
  *(((char**) (arr->arr))[0]) = ((char) (i_6 >> 0));
  *(((char**) (arr->arr))[1]) = ((char) (i_6 >> 8));
  *(((char**) (arr->arr))[2]) = ((char) (i_6 >> 16));
  *(((char**) (arr->arr))[3]) = ((char) (i_6 >> 24));
  return arr;
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

  client(host, 1, 1);


  return 0;
}
