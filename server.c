/*
 * Includes
 */
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <netinet/in.h>
#include <stdio.h>
#include <errno.h>

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
 * Structs
 */
struct SocketAddressIP4;
struct SocketAddressIP6;

typedef struct SocketAddressIP4 {
  int sin4_addr;
  int sin4_port;
} SocketAddressIP4;

typedef struct SocketAddressIP6 {
  SPLArray_char* sin6_addr;
  int sin6_flowinfo;
  int sin6_port;
  int sin6_scope_id;
} SocketAddressIP6;

/*
 * Procedures
 */
int Main (SPLArray_char* args);
bool bind4 (int fd, struct SocketAddressIP4* address);
bool bind6 (int fd_1, struct SocketAddressIP6* address_1);
int checkPacket (SPLArray_char* packet);
SPLArray_char* constructPacket (SPLArray_char* req);
SPLArray_int* copy (SPLArray_int* a);
int create_socket (int inet_type, int socket_type, int protocol);
int gclose (int fd_3);
struct SocketAddressIP4* get_address4 (SPLArray_char* node, SPLArray_char* service);
struct SocketAddressIP6* get_address6 (SPLArray_char* node_1, SPLArray_char* service_1);
int gopen (SPLArray_char* pathname, int flags);
int gread (int fd_5, SPLArray_char* buffer);
int greadOffset (int fd_6, SPLArray_char* buffer_1, int offset);
int gwrite (int fd_7, SPLArray_char* buffer_2);
SPLArray_char* intToByteArray (int i_5);
void server (SPLArray_char* host);
int udp_recv4 (int fd_9, SPLArray_char* msg, struct SocketAddressIP4* from);
int udp_recv6 (int fd_10, SPLArray_char* msg_1, struct SocketAddressIP6* from_1);
int udp_send4 (int fd_11, SPLArray_char* msg_2, int len, struct SocketAddressIP4* address_4);
int udp_send6 (int fd_12, SPLArray_char* msg_3, int len_1, struct SocketAddressIP6* address_5);

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
  int i_2;
  
  tmp_1 = newSPLArray_int( (a->length));
  b = tmp_1;
  i_2 = 0;
  while (true) {
    if (!((i_2 < (a->length)))) {
      break;
    }
    (b->arr[i_2]) = (a->arr[i_2]);
    i_2 = (i_2 + 1);
  }
  return b;
}

SPLArray_char* intToByteArray (int i_5) {
  SPLArray_char* arr;
  SPLArray_char* tmp_2;
  
  tmp_2 = newSPLArray_char( 4);
  arr = tmp_2;
  (arr->arr[0]) = ((char) (i_5 >> 0));
  (arr->arr[1]) = ((char) (i_5 >> 8));
  (arr->arr[2]) = ((char) (i_5 >> 16));
  (arr->arr[3]) = ((char) (i_5 >> 24));
  return arr;
}

void server (SPLArray_char* host) {
  SPLArray_char* toSend;
  int tmp_5;
  SPLArray_char* tmp_4;
  SPLArray_char* tmp_3;
  int sent;
  int recd;
  SPLArray_char* port;
  int fd_8;
  SPLArray_char* content;
  int closed;
  bool bound;
  struct SocketAddressIP4* addr;
  
  tmp_3 = newSPLArray_char( 4);
  port = tmp_3;
  (port->arr[0]) = ((char) 49);
  (port->arr[1]) = ((char) 50);
  (port->arr[2]) = ((char) 51);
  (port->arr[3]) = ((char) 0);
  addr = get_address4(host, port);
  free(port);

  //  gwrite(1, host);
  // printf("%x\n", addr->sin4_addr);

  if ((addr == NULL)) {
    return;
  }
  fd_8 = create_socket(PF_INET, SOCK_DGRAM, IPPROTO_UDP);
  if ((fd_8 < 0)) {
    free(addr);

    return;
  }
  bound = bind4(fd_8, addr);
  if ((!bound)) {
    free(addr);
    printf("error: %s\n", strerror(errno));
    return;
  }
  tmp_4 = newSPLArray_char( 12);
  content = tmp_4;
  recd = udp_recv4(fd_8, content, addr);
  if ((!(recd == 12))) {
    free(addr);
    
    free(content);
    
    return;
  }
  tmp_5 = checkPacket(content);
  if ((!(tmp_5 == 1))) {
    free(addr);
    
    free(content);
    
    return;
  }
  toSend = constructPacket(content);
  sent = udp_send4(fd_8, toSend, (toSend->length), addr);
  closed = gclose(fd_8);
  free(addr);
  
  free(content);
  
  free(toSend);
  
  if ((!(sent == (toSend->length)))) {
    return;
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

