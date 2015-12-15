#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <errno.h>
#include <string.h>

#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
//#include <arpa/inet.h>

/*
 * Preloaded Code
 */

typedef struct {
  int length;
  char arr[];
} SPLArray_char;

SPLArray_char* _newSPLArray_char(int size) {
  SPLArray_char* a = (SPLArray_char*)malloc(sizeof(SPLArray_char) + size * sizeof(char));
  assert(a != NULL);
  a->length = size;
  return a;
}

typedef struct SocketAddressIP4 {
  //int sin4_addr_lower;
  //int sin4_addr_upper;
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

void to_grass_addr(struct sockaddr_in* c, struct SocketAddressIP4* address) {
  address->sin4_port = c->sin_port;
  //address->sin4_addr_upper = (int)(c->sin_addr.s_addr >> 32);
  //address->sin4_addr_lower = (int)(c->sin_addr.s_addr);
  address->sin4_addr = c->sin_addr.s_addr;
}

void from_grass_addr(struct SocketAddressIP4* address, struct sockaddr_in* c) {
  c->sin_family = AF_INET;
  c->sin_port = (short) address->sin4_port;
  //c->sin_addr.s_addr = (((long)address->sin4_addr_upper) << 32) | address->sin4_addr_lower;
  c->sin_addr.s_addr = address->sin4_addr;
  c->sin_zero[0] = 0;  c->sin_zero[1] = 0;
  c->sin_zero[2] = 0;  c->sin_zero[3] = 0;
  c->sin_zero[4] = 0;  c->sin_zero[5] = 0;
  c->sin_zero[6] = 0;  c->sin_zero[7] = 0;
}

void to_grass_addr6(struct sockaddr_in6* c, struct SocketAddressIP6* address) {
  address->sin6_port = c->sin6_port;
  address->sin6_flowinfo = c->sin6_flowinfo;
  address->sin6_scope_id = c->sin6_scope_id;
  for(int i = 0; i < 16; i++) {
    address->sin6_addr->arr[i] = c->sin6_addr.s6_addr[i];
  }
}

void from_grass_addr6(struct SocketAddressIP6* address, struct sockaddr_in6* c) {
  c->sin6_family = AF_INET6;
  c->sin6_port = (short)address->sin6_port;
  c->sin6_flowinfo = address->sin6_flowinfo;
  c->sin6_scope_id = address->sin6_scope_id;
  for (int i = 0; i < 16; i++) {
    c->sin6_addr.s6_addr[i] = address->sin6_addr->arr[i];
  }
}

struct SocketAddressIP4* get_address4(SPLArray_char* node, SPLArray_char* service) {
  struct addrinfo hint;
  memset(&hint, 0, sizeof hint);
  hint.ai_family = AF_INET;
  hint.ai_socktype = SOCK_DGRAM; //SOCK_STREAM
  hint.ai_protocol = IPPROTO_UDP; //IPPROTO_TCP
  struct addrinfo *servinfo = NULL;
  int rv;
  if (node == NULL) {
    rv = getaddrinfo(NULL, service->arr, &hint, &servinfo);
  } else {
    rv = getaddrinfo(node->arr, service->arr, &hint, &servinfo);
  }
  if (rv != 0) {
    return NULL;
  } else {
    struct addrinfo *p;
    for(p = servinfo; p != NULL; p = p->ai_next) {
      if (p->ai_family == AF_INET) {
	struct SocketAddressIP4* address = malloc(sizeof(struct SocketAddressIP4));
	assert(address != NULL);
	struct sockaddr_in* a = (struct sockaddr_in*)p->ai_addr;
	to_grass_addr(a, address);
	freeaddrinfo(servinfo);
	return address;
      }
    }
    freeaddrinfo(servinfo);
    return NULL;
  }
}

struct SocketAddressIP6* get_address6(SPLArray_char* node, SPLArray_char* service) {
  struct addrinfo hint;
  memset(&hint, 0, sizeof hint);
  hint.ai_family = AF_INET6;
  hint.ai_socktype = SOCK_DGRAM; //SOCK_STREAM
  hint.ai_protocol = IPPROTO_UDP; //IPPROTO_TCP
  struct addrinfo *servinfo = NULL;
  //TODO
  int rv;
  if (node == NULL) {
    rv = getaddrinfo(NULL, service->arr, &hint, &servinfo);
  } else {
    rv = getaddrinfo(node->arr, service->arr, &hint, &servinfo);
  }
  if (rv != 0) {
    return NULL;
  } else {
    struct addrinfo *p;
    for(p = servinfo; p != NULL; p = p->ai_next) {
      if (p->ai_family == AF_INET6) {
	struct SocketAddressIP6* address = malloc(sizeof(struct SocketAddressIP6));
	assert(address != NULL);
	address->sin6_addr = _newSPLArray_char(16);
	struct sockaddr_in6* a = (struct sockaddr_in6*)p->ai_addr;
	to_grass_addr6(a, address);
	freeaddrinfo(servinfo);
	return address;
      }
    }
    freeaddrinfo(servinfo);
    return NULL;
  }
}

bool bind4(int fd, struct SocketAddressIP4* address) {
  struct sockaddr_in sa;
  from_grass_addr(address, &sa);
  //printf("IP address is: %s\n", inet_ntoa(sa.sin_addr));
  //printf("port is: %d\n", (int) ntohs(sa.sin_port));
  return bind(fd, (struct sockaddr *)&sa, sizeof sa) == 0;
}

bool bind6(int fd, struct SocketAddressIP6* address) {
  struct sockaddr_in6 sa;
  from_grass_addr6(address, &sa);
  return bind(fd, (struct sockaddr *)&sa, sizeof sa) == 0;
}

int create_socket(int inet_type, int socket_type, int protocol) {
  return socket(inet_type, socket_type, protocol);
}

int udp_recv4(int fd, SPLArray_char* msg, struct SocketAddressIP4* from) {
  struct sockaddr_in sa;
  int len = sizeof sa;
  int res = recvfrom(fd, msg->arr, msg->length, 0, (struct sockaddr*)&sa, &len);
  if (res >= 0) {
    assert(len == (sizeof sa));
    to_grass_addr(&sa, from);
  }
  return res;
}

int udp_recv6(int fd, SPLArray_char* msg, struct SocketAddressIP6* from) {
  struct sockaddr_in6 sa;
  int len = sizeof sa;
  int res = recvfrom(fd, msg->arr, msg->length, 0, (struct sockaddr*)&sa, &len);
  if (res >= 0) {
    assert(len == (sizeof sa));
    to_grass_addr6(&sa, from);
  }
  return res;
}

int udp_send4(int fd, SPLArray_char* msg, int len, struct SocketAddressIP4* address) {
  struct sockaddr_in sa;
  from_grass_addr(address, &sa);
  return sendto(fd, msg->arr, len, 0, (struct sockaddr*) &sa, sizeof sa);
}

int udp_send6(int fd, SPLArray_char* msg, int len, struct SocketAddressIP6* address) {
  struct sockaddr_in6 sa;
  from_grass_addr6(address, &sa);
  return sendto(fd, msg->arr, len, 0, (struct sockaddr*) &sa, sizeof sa);
}
