/*
 * Includes
 */
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <netinet/in.h>

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
int client (SPLArray_char* host, int mode, int version);
SPLArray_char* constructPacket (int mode_1, int version_1);
SPLArray_int* copy (SPLArray_int* a);
SPLArray_char* copyByte (SPLArray_char* a_1);
int create_socket (int inet_type, int socket_type, int protocol);
int gclose (int fd_4);
struct SocketAddressIP4* get_address4 (SPLArray_char* node, SPLArray_char* service);
struct SocketAddressIP6* get_address6 (SPLArray_char* node_1, SPLArray_char* service_1);
int gopen (SPLArray_char* pathname, int flags_1);
int gread (int fd_6, SPLArray_char* buffer_1);
int greadOffset (int fd_7, SPLArray_char* buffer_2, int offset);
int gwrite (int fd_8, SPLArray_char* buffer_3);
SPLArray_char* intToByteArray (int i_8);
int udp_recv4 (int fd_9, SPLArray_char* msg, struct SocketAddressIP4* from);
int udp_recv6 (int fd_10, SPLArray_char* msg_1, struct SocketAddressIP6* from_1);
int udp_send4 (int fd_11, SPLArray_char* msg_2, int len, struct SocketAddressIP4* address_4);
int udp_send6 (int fd_12, SPLArray_char* msg_3, int len_1, struct SocketAddressIP6* address_5);

int Main (SPLArray_char* args) {
  int res;
  if ((!((args->length) == 4))) {
    return 1;
  }
  res = client(args, 1, 1);
  return res;
}

int client (SPLArray_char* host, int mode, int version) {
  int time;
  SPLArray_char* tmp_1;
  SPLArray_char* tmp;
  int temp;
  bool success_2;
  int sent;
  SPLArray_char* response;
  int res_1;
  int received;
  SPLArray_char* port;
  SPLArray_char* packet;
  int flags;
  int fd_2;
  int closed;
  SPLArray_char* buffer;
  struct SocketAddressIP4* addr;
  
  flags = 0;
  fd_2 = create_socket(PF_INET, SOCK_DGRAM, IPPROTO_UDP);
  if ((fd_2 == (-1))) {
    return 1;
  }
  tmp = newSPLArray_char( 4);
  port = tmp;
  (port->arr[0]) = ((char) 52);
  (port->arr[1]) = ((char) 52);
  (port->arr[2]) = ((char) 52);
  (port->arr[3]) = ((char) 0);
  addr = get_address4(host, port);
  free(port);
  
  if ((addr == NULL)) {
    return 2;
  }
  success_2 = bind4(fd_2, addr);
  if ((!success_2)) {
    free(addr);
    
    return 3;
  }
  packet = constructPacket(mode, version);
  buffer = copyByte(packet);
  sent = udp_send4(fd_2, buffer, (buffer->length), addr);
  tmp_1 = newSPLArray_char( 12);
  response = tmp_1;
  received = udp_recv4(fd_2, response, addr);
  closed = gclose(fd_2);
  free(addr);
  
  res_1 = ((int) (((response->arr[9]) * ((char) 1000000000)) + ((response->arr[10]) * (((char) 1000000000) >> 32))));
  free(packet);
  
  free(response);
  
  free(buffer);
  
  temp = gclose(fd_2);
  return res_1;
}

SPLArray_char* constructPacket (int mode_1, int version_1) {
  SPLArray_char* packet_1;
  SPLArray_char* tmp_2;
  int i_1;
  
  tmp_2 = newSPLArray_char( 12);
  packet_1 = tmp_2;
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
  SPLArray_int* tmp_3;
  int i_3;
  
  tmp_3 = newSPLArray_int( (a->length));
  b = tmp_3;
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
  SPLArray_char* tmp_4;
  int i_5;
  
  tmp_4 = newSPLArray_char( (a_1->length));
  b_1 = tmp_4;
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
  SPLArray_char* tmp_5;
  
  tmp_5 = newSPLArray_char( 4);
  arr = tmp_5;
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

