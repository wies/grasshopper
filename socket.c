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
 * Utility function I added
 */

struct sockaddr_in* sockConverter (struct SocketAddressIP4* convertMe);

struct sockaddr_in* sockConverter (struct SocketAddressIP4* convertMe){
  struct sockaddr_in* final;
  struct in_addr addr;
  addr.s_addr = convertMe->sin4_addr;
  final->sin_family = AF_INET;
  final->sin_port = convertMe->sin4_port;
  final->sin_addr = addr;
  return final;
}

/*
 * Procedures
 */
bool bind4 (int fd, struct SocketAddressIP4* address);
bool bind6 (int fd_1, struct SocketAddressIP6* address_1);
int create_socket (int inet_type, int socket_type, int protocol);
struct SocketAddressIP4* get_address4 (SPLArray_char* node, SPLArray_char* service);
struct SocketAddressIP6* get_address6 (SPLArray_char* node_1, SPLArray_char* service_1);
int udp_recv4 (int fd_3, SPLArray_char* msg, struct SocketAddressIP4* from);
int udp_recv6 (int fd_4, SPLArray_char* msg_1, struct SocketAddressIP6* from_1);
int udp_send4 (int fd_5, SPLArray_char* msg_2, int len, struct SocketAddressIP4* address_4);
int udp_send6 (int fd_6, SPLArray_char* msg_3, int len_1, struct SocketAddressIP6* address_5);

bool bind4 (int fd, struct SocketAddressIP4* address){
  return bind(fd, (struct sockaddr *) sockConverter(address), sizeof(address));
}

int create_socket (int inet_type, int socket_type, int protocol){
  return socket(inet_type, socket_type, protocol);
}

int udp_recv4 (int fd3, SPLArray_char* msg, struct SocketAddressIP4* from){
  unsigned int temp = (unsigned int) sizeof(from);
  return (int) recvfrom(fd3, msg->arr, sizeof(char) * msg->length, 0, (struct sockaddr *) sockConverter(from), &temp);
}

int udp_send4 (int fd5, SPLArray_char* msg_2, int len, struct SocketAddressIP4* address_4){
  return sendto(fd5, msg_2->arr, len, 0, (struct sockaddr *) sockConverter(address_4), sizeof(address_4));
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

