/*
 * Includes
 */
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <fcntl.h>
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
int accept4 (int fd, struct SocketAddressIP4* address);
int accept6 (int fd_1, struct SocketAddressIP6* address_1);
SPLArray_char* askFilename ();
int atoiFrom (SPLArray_char* str, int startIdx);
int atoiG (SPLArray_char* str_1);
bool authenticate (int cmdFd);
bool bind4 (int fd_2, struct SocketAddressIP4* address_2);
bool bind6 (int fd_3, struct SocketAddressIP6* address_3);
bool checkServerResponse (SPLArray_char* response, SPLArray_int* acceptables_1);
int client (bool upload_1);
SPLArray_char* concat (SPLArray_char* str1, SPLArray_char* str2);
bool connect4 (int fd_5, struct SocketAddressIP4* address_4);
bool connect6 (int fd_6, struct SocketAddressIP6* address_5);
int connectTo (SPLArray_char* ip, SPLArray_char* port_1);
int create_socket (int inet_type, int socket_type, int protocol);
int doWeUpload ();
bool downloadFile (int cmdFd_1, int dataFD, SPLArray_char* filename_2);
bool equals (SPLArray_char* first, SPLArray_char* second);
int fileSize (SPLArray_char* pathname);
int gclose (int fd_9);
struct SocketAddressIP4* get_address4 (SPLArray_char* node, SPLArray_char* service);
struct SocketAddressIP6* get_address6 (SPLArray_char* node_1, SPLArray_char* service_1);
int ggets (SPLArray_char* buffer_1);
bool glisten (int fd_10, int backlog);
int gopen (SPLArray_char* pathname_1, int flags);
int gputs (SPLArray_char* buffer_2);
int gread (int fd_12, SPLArray_char* buffer_3);
int greadOffset (int fd_13, SPLArray_char* buffer_4, int offset);
int gwrite (int fd_14, SPLArray_char* buffer_5);
int gwrite2 (int fd_15, SPLArray_char* buffer_6, int size_2);
int setupDataConnection (int cmdFd_2, SPLArray_char* port_2);
int strcat (SPLArray_char* str1_1, SPLArray_char* str2_1);
int strcmp (SPLArray_char* s1, SPLArray_char* s2);
SPLArray_char* strconcat (SPLArray_char* str1_2, SPLArray_char* str2_2);
SPLArray_char* strdup (SPLArray_char* str_2);
int strlen (SPLArray_char* str_3);
int tcp_recv (int fd_16, SPLArray_char* msg);
int tcp_send (int fd_17, SPLArray_char* msg_1, int len);
int udp_recv4 (int fd_18, SPLArray_char* msg_2, struct SocketAddressIP4* from);
int udp_recv6 (int fd_19, SPLArray_char* msg_3, struct SocketAddressIP6* from_1);
int udp_send4 (int fd_20, SPLArray_char* msg_4, int len_1, struct SocketAddressIP4* address_8);
int udp_send6 (int fd_21, SPLArray_char* msg_5, int len_2, struct SocketAddressIP6* address_9);
bool uploadFile (int cmdFd_3, int dataFD_2, SPLArray_char* filename_3);

int Main (SPLArray_char* args) {
  int res;
  int upload;
  
  upload = doWeUpload();
  if ((upload == 1)) {
    res = client(true);
  } else {
    if ((upload == 0)) {
      res = client(false);
    } else {
      res = (-1);
    }
  }
  return res;
}

SPLArray_char* askFilename () {
  SPLArray_char* fn;
  int written;
  int tmp_2;
  SPLArray_char* tmp_1;
  SPLArray_char* tmp;
  SPLArray_char* text;
  int numChars;
  SPLArray_char* filename;
  
  tmp = newSPLArray_char( 100);
  filename = tmp;
  tmp_1 = newSPLArray_char( 24);
  text = tmp_1;
  (text->arr[0]) = ((char) 105);
  (text->arr[1]) = ((char) 110);
  (text->arr[2]) = ((char) 112);
  (text->arr[3]) = ((char) 117);
  (text->arr[4]) = ((char) 116);
  (text->arr[5]) = ((char) 32);
  (text->arr[6]) = ((char) 116);
  (text->arr[7]) = ((char) 104);
  (text->arr[8]) = ((char) 101);
  (text->arr[9]) = ((char) 32);
  (text->arr[10]) = ((char) 102);
  (text->arr[11]) = ((char) 105);
  (text->arr[12]) = ((char) 108);
  (text->arr[13]) = ((char) 101);
  (text->arr[14]) = ((char) 32);
  (text->arr[15]) = ((char) 110);
  (text->arr[16]) = ((char) 97);
  (text->arr[17]) = ((char) 109);
  (text->arr[18]) = ((char) 101);
  (text->arr[19]) = ((char) 58);
  (text->arr[20]) = ((char) 0);
  written = gputs(text);
  tmp_2 = strlen(text);
  if ((!(written == tmp_2))) {
    free(text);
    
    free(filename);
    
    return NULL;
  }
  free(text);
  
  numChars = ggets(filename);
  if (((numChars >= 100) || (numChars <= 1))) {
    free(filename);
    
    return NULL;
  }
  (filename->arr[(numChars - 1)]) = ((char) 0);
  return filename;
}

int atoiFrom (SPLArray_char* str, int startIdx) {
  int res_1;
  bool isPositive;
  int i;
  bool foundStart;
  bool foundEnd;
  int digit;
  
  res_1 = 0;
  i = startIdx;
  if ((i > (str->length))) {
    i = (str->length);
  }
  foundStart = false;
  foundEnd = false;
  isPositive = true;
  while (true) {
    if (!(((i < (str->length)) && (!foundStart)))) {
      break;
    }
    if ((((((((str->arr[i]) == ((char) 9)) || ((str->arr[i]) == ((char) 10))) || ((str->arr[i]) == ((char) 11))) || ((str->arr[i]) == ((char) 12))) || ((str->arr[i]) == ((char) 13))) || ((str->arr[i]) == ((char) 32)))) {
      i = (i + 1);
    } else {
      foundStart = true;
    }
  }
  if ((i < (str->length))) {
    if (((str->arr[i]) == ((char) 45))) {
      isPositive = false;
      i = (i + 1);
    }
  }
  while (true) {
    if (!(((i < (str->length)) && (!foundEnd)))) {
      break;
    }
    if ((((str->arr[i]) >= ((char) 48)) && ((str->arr[i]) <= ((char) 57)))) {
      digit = ((int) ((str->arr[i]) - ((char) 48)));
      res_1 = (res_1 * 10);
      res_1 = (res_1 + digit);
      i = (i + 1);
    } else {
      foundEnd = true;
    }
  }
  if ((!isPositive)) {
    res_1 = ((-1) * res_1);
  }
  return res_1;
}

int atoiG (SPLArray_char* str_1) {
  int res_2;
  res_2 = atoiFrom(str_1, 0);
  return res_2;
  return res_2;
}

bool authenticate (int cmdFd) {
  bool success;
  SPLArray_char* userMsg;
  SPLArray_int* tmp_8;
  SPLArray_char* tmp_7;
  SPLArray_char* tmp_6;
  SPLArray_int* tmp_5;
  SPLArray_char* tmp_4;
  SPLArray_char* tmp_3;
  int sent;
  SPLArray_char* passMsg;
  SPLArray_char* okMsg;
  int ok;
  bool checked;
  SPLArray_int* acceptables;
  SPLArray_int* acceptThese;
  
  tmp_3 = newSPLArray_char( 12);
  userMsg = tmp_3;
  (userMsg->arr[0]) = ((char) 85);
  (userMsg->arr[1]) = ((char) 83);
  (userMsg->arr[2]) = ((char) 69);
  (userMsg->arr[3]) = ((char) 82);
  (userMsg->arr[4]) = ((char) 32);
  (userMsg->arr[5]) = ((char) 112);
  (userMsg->arr[6]) = ((char) 111);
  (userMsg->arr[7]) = ((char) 116);
  (userMsg->arr[8]) = ((char) 97);
  (userMsg->arr[9]) = ((char) 116);
  (userMsg->arr[10]) = ((char) 111);
  (userMsg->arr[11]) = ((char) 0);
  sent = tcp_send(cmdFd, userMsg, 12);
  free(userMsg);
  
  tmp_4 = newSPLArray_char( 4);
  okMsg = tmp_4;
  ok = tcp_recv(cmdFd, okMsg);
  tmp_5 = newSPLArray_int( 5);
  acceptables = tmp_5;
  (acceptables->arr[0]) = 200;
  (acceptables->arr[1]) = 230;
  (acceptables->arr[2]) = 234;
  (acceptables->arr[3]) = 300;
  (acceptables->arr[4]) = 331;
  checked = checkServerResponse(okMsg, acceptables);
  free(okMsg);
  
  free(acceptables);
  
  if ((!checked)) {
    return false;
  }
  tmp_6 = newSPLArray_char( 15);
  passMsg = tmp_6;
  (passMsg->arr[0]) = ((char) 80);
  (passMsg->arr[1]) = ((char) 65);
  (passMsg->arr[2]) = ((char) 83);
  (passMsg->arr[3]) = ((char) 83);
  (passMsg->arr[4]) = ((char) 32);
  (passMsg->arr[5]) = ((char) 97);
  (passMsg->arr[6]) = ((char) 110);
  (passMsg->arr[7]) = ((char) 111);
  (passMsg->arr[8]) = ((char) 110);
  (passMsg->arr[9]) = ((char) 121);
  (passMsg->arr[10]) = ((char) 109);
  (passMsg->arr[11]) = ((char) 111);
  (passMsg->arr[12]) = ((char) 117);
  (passMsg->arr[13]) = ((char) 115);
  (passMsg->arr[14]) = ((char) 0);
  sent = tcp_send(cmdFd, passMsg, 15);
  free(passMsg);
  
  tmp_7 = newSPLArray_char( 4);
  okMsg = tmp_7;
  ok = tcp_recv(cmdFd, okMsg);
  tmp_8 = newSPLArray_int( 4);
  acceptThese = tmp_8;
  (acceptThese->arr[0]) = 200;
  (acceptThese->arr[1]) = 202;
  (acceptThese->arr[2]) = 230;
  (acceptThese->arr[3]) = 234;
  checked = checkServerResponse(okMsg, acceptThese);
  free(okMsg);
  
  free(acceptThese);
  
  if ((!checked)) {
    return false;
  }
  return true;
}

bool checkServerResponse (SPLArray_char* response, SPLArray_int* acceptables_1) {
  bool success_3;
  int i_2;
  int ack;
  
  i_2 = 0;
  ack = atoiG(response);
  success_3 = false;
  while (true) {
    if (!((i_2 < (acceptables_1->length)))) {
      break;
    }
    if ((ack == (acceptables_1->arr[i_2]))) {
      success_3 = true;
    }
    i_2 = (i_2 + 1);
  }
  return success_3;
}

int client (bool upload_1) {
  int res_3;
  SPLArray_char* tmp_10;
  SPLArray_char* tmp_9;
  bool success_4;
  int sent_1;
  SPLArray_char* quitMsg;
  SPLArray_char* port;
  SPLArray_char* filename_1;
  int fd_4;
  int connectedDataFD;
  int closeFD;
  int closeConn;
  bool authenticated;
  
  tmp_9 = newSPLArray_char( 5);
  port = tmp_9;
  (port->arr[0]) = ((char) 52);
  (port->arr[1]) = ((char) 52);
  (port->arr[2]) = ((char) 52);
  (port->arr[3]) = ((char) 52);
  (port->arr[4]) = ((char) 0);
  fd_4 = connectTo(NULL, port);
  if ((fd_4 == (-1))) {
    free(port);
    
    return 2;
  }
  (port->arr[0]) = ((char) 52);
  (port->arr[1]) = ((char) 52);
  (port->arr[2]) = ((char) 52);
  (port->arr[3]) = ((char) 48);
  (port->arr[4]) = ((char) 0);
  connectedDataFD = setupDataConnection(fd_4, port);
  free(port);
  
  if ((connectedDataFD == (-1))) {
    return 3;
  }
  authenticated = authenticate(fd_4);
  if ((!authenticated)) {
    return 4;
  }
  filename_1 = askFilename();
  if ((filename_1 == NULL)) {
    return 5;
  }
  success_4 = false;
  if (upload_1) {
    success_4 = uploadFile(fd_4, connectedDataFD, filename_1);
  } else {
    success_4 = downloadFile(fd_4, connectedDataFD, filename_1);
  }
  free(filename_1);
  
  if ((!success_4)) {
    return 6;
  }
  closeConn = gclose(connectedDataFD);
  if ((closeConn < 0)) {
    return 22;
  }
  tmp_10 = newSPLArray_char( 5);
  quitMsg = tmp_10;
  (quitMsg->arr[0]) = ((char) 81);
  (quitMsg->arr[1]) = ((char) 85);
  (quitMsg->arr[2]) = ((char) 73);
  (quitMsg->arr[3]) = ((char) 84);
  (quitMsg->arr[4]) = ((char) 0);
  sent_1 = tcp_send(fd_4, quitMsg, 5);
  free(quitMsg);
  
  closeFD = gclose(fd_4);
  if ((closeFD < 0)) {
    return 21;
  }
  return 0;
}

SPLArray_char* concat (SPLArray_char* str1, SPLArray_char* str2) {
  SPLArray_char* res_4;
  SPLArray_char* tmp_11;
  int i_3;
  SPLArray_char* copy;
  
  
  tmp_11 = newSPLArray_char( ((str1->length) + (str2->length)));
  copy = tmp_11;
  i_3 = 0;
  while (true) {
    if (!((i_3 < (str1->length)))) {
      break;
    }
    (copy->arr[i_3]) = (str1->arr[i_3]);
    i_3 = (i_3 + 1);
  }
  while (true) {
    if (!((i_3 < ((str1->length) + (str2->length))))) {
      break;
    }
    (copy->arr[i_3]) = (str2->arr[(i_3 - (str1->length))]);
    i_3 = (i_3 + 1);
  }
  return copy;
}

int connectTo (SPLArray_char* ip, SPLArray_char* port_1) {
  int fd_7;
  bool tmp_12;
  int closing;
  struct SocketAddressIP4* addr;
  
  fd_7 = create_socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
  if ((fd_7 == (-1))) {
    return (-1);
  }
  addr = get_address4(ip, port_1);
  if ((addr == NULL)) {
    return (-1);
  }
  tmp_12 = connect4(fd_7, addr);
  if (tmp_12) {
    free(addr);
    
    return fd_7;
  } else {
    free(addr);
    
    closing = gclose(fd_7);
    return (-1);
  }
  return fd_7;
}

int doWeUpload () {
  int res_5;
  int written_1;
  SPLArray_char* updown;
  SPLArray_char* uChar;
  int tmp_16;
  SPLArray_char* tmp_15;
  SPLArray_char* tmp_14;
  SPLArray_char* tmp_13;
  int textLen;
  SPLArray_char* text_1;
  int numChars_1;
  
  tmp_13 = newSPLArray_char( 2);
  updown = tmp_13;
  tmp_14 = newSPLArray_char( 28);
  text_1 = tmp_14;
  (text_1->arr[0]) = ((char) 117);
  (text_1->arr[1]) = ((char) 112);
  (text_1->arr[2]) = ((char) 108);
  (text_1->arr[3]) = ((char) 111);
  (text_1->arr[4]) = ((char) 97);
  (text_1->arr[5]) = ((char) 100);
  (text_1->arr[6]) = ((char) 32);
  (text_1->arr[7]) = ((char) 40);
  (text_1->arr[8]) = ((char) 117);
  (text_1->arr[9]) = ((char) 41);
  (text_1->arr[10]) = ((char) 32);
  (text_1->arr[11]) = ((char) 111);
  (text_1->arr[12]) = ((char) 114);
  (text_1->arr[13]) = ((char) 32);
  (text_1->arr[14]) = ((char) 100);
  (text_1->arr[15]) = ((char) 111);
  (text_1->arr[16]) = ((char) 119);
  (text_1->arr[17]) = ((char) 110);
  (text_1->arr[18]) = ((char) 108);
  (text_1->arr[19]) = ((char) 111);
  (text_1->arr[20]) = ((char) 97);
  (text_1->arr[21]) = ((char) 100);
  (text_1->arr[22]) = ((char) 32);
  (text_1->arr[23]) = ((char) 40);
  (text_1->arr[24]) = ((char) 100);
  (text_1->arr[25]) = ((char) 41);
  (text_1->arr[26]) = ((char) 58);
  (text_1->arr[27]) = ((char) 0);
  written_1 = gputs(text_1);
  textLen = strlen(text_1);
  free(text_1);
  
  if ((!(written_1 == textLen))) {
    free(updown);
    
    return (-1);
  } else {
    numChars_1 = ggets(updown);
    if ((numChars_1 == 1)) {
      (updown->arr[1]) = ((char) 0);
      tmp_15 = newSPLArray_char( 2);
      uChar = tmp_15;
      (uChar->arr[0]) = ((char) 117);
      (uChar->arr[1]) = ((char) 0);
      tmp_16 = strcmp(uChar, updown);
      if ((tmp_16 == 0)) {
        free(uChar);
        
        free(updown);
        
        return 1;
      } else {
        free(uChar);
        
        free(updown);
        
        return 0;
      }
    } else {
      free(updown);
      
      return (-1);
    }
  }
  return res_5;
}

bool downloadFile (int cmdFd_1, int dataFD, SPLArray_char* filename_2) {
  bool success_7;
  int written_2;
  SPLArray_int* tmp_25;
  SPLArray_char* tmp_24;
  SPLArray_int* tmp_23;
  SPLArray_char* tmp_22;
  SPLArray_char* tmp_21;
  SPLArray_char* tmp_20;
  SPLArray_int* tmp_19;
  SPLArray_char* tmp_18;
  SPLArray_char* tmp_17;
  SPLArray_char* sizeMsg;
  SPLArray_char* sizeBuff;
  int size;
  int sent_2;
  int saveFD;
  SPLArray_char* recvMsg;
  int recvData;
  SPLArray_int* pleaseAccept;
  SPLArray_char* okMsg_1;
  int ok_1;
  int copied;
  int cmdSize;
  int close;
  bool checked_1;
  SPLArray_char* buffer;
  SPLArray_int* acceptThese_1;
  
  if ((((filename_2->length) <= 0) || ((filename_2->length) > (65535 - 6)))) {
    return false;
  }
  cmdSize = (6 + (filename_2->length));
  tmp_17 = newSPLArray_char( cmdSize);
  sizeMsg = tmp_17;
  (sizeMsg->arr[0]) = ((char) 83);
  (sizeMsg->arr[1]) = ((char) 73);
  (sizeMsg->arr[2]) = ((char) 90);
  (sizeMsg->arr[3]) = ((char) 69);
  (sizeMsg->arr[4]) = ((char) 32);
  (sizeMsg->arr[5]) = ((char) 0);
  copied = strcat(filename_2, sizeMsg);
  sent_2 = tcp_send(cmdFd_1, sizeMsg, cmdSize);
  free(sizeMsg);
  
  tmp_18 = newSPLArray_char( 128);
  sizeBuff = tmp_18;
  recvData = tcp_recv(cmdFd_1, sizeBuff);
  tmp_19 = newSPLArray_int( 1);
  pleaseAccept = tmp_19;
  (pleaseAccept->arr[0]) = 213;
  checked_1 = checkServerResponse(sizeBuff, pleaseAccept);
  free(pleaseAccept);
  
  if ((!checked_1)) {
    free(sizeBuff);
    
    return false;
  }
  size = atoiFrom(sizeBuff, 4);
  free(sizeBuff);
  
  if (((size <= 0) || (size > 65535))) {
    return false;
  }
  tmp_20 = newSPLArray_char( size);
  buffer = tmp_20;
  tmp_21 = newSPLArray_char( cmdSize);
  recvMsg = tmp_21;
  (recvMsg->arr[0]) = ((char) 82);
  (recvMsg->arr[1]) = ((char) 69);
  (recvMsg->arr[2]) = ((char) 84);
  (recvMsg->arr[3]) = ((char) 82);
  (recvMsg->arr[4]) = ((char) 32);
  (recvMsg->arr[5]) = ((char) 0);
  copied = strcat(filename_2, recvMsg);
  sent_2 = tcp_send(cmdFd_1, recvMsg, cmdSize);
  free(recvMsg);
  
  tmp_22 = newSPLArray_char( 4);
  okMsg_1 = tmp_22;
  ok_1 = tcp_recv(cmdFd_1, okMsg_1);
  tmp_23 = newSPLArray_int( 2);
  acceptThese_1 = tmp_23;
  (acceptThese_1->arr[0]) = 200;
  (acceptThese_1->arr[1]) = 150;
  checked_1 = checkServerResponse(okMsg_1, acceptThese_1);
  free(okMsg_1);
  
  free(acceptThese_1);
  
  if ((!checked_1)) {
    free(buffer);
    
    return false;
  }
  recvData = tcp_recv(dataFD, buffer);
  tmp_24 = newSPLArray_char( 4);
  okMsg_1 = tmp_24;
  ok_1 = tcp_recv(cmdFd_1, okMsg_1);
  tmp_25 = newSPLArray_int( 3);
  pleaseAccept = tmp_25;
  (pleaseAccept->arr[0]) = 200;
  (pleaseAccept->arr[1]) = 226;
  (pleaseAccept->arr[2]) = 250;
  checked_1 = checkServerResponse(okMsg_1, pleaseAccept);
  free(okMsg_1);
  
  free(pleaseAccept);
  
  if ((!checked_1)) {
    free(buffer);
    
    return false;
  }
  if ((recvData < 0)) {
    free(buffer);
    
    return false;
  }
  saveFD = gopen(filename_2, ((O_CREAT | O_WRONLY) | O_TRUNC));
  if ((saveFD < 0)) {
    free(buffer);
    
    return false;
  }
  written_2 = gwrite(saveFD, buffer);
  free(buffer);
  
  if ((written_2 < 0)) {
    return false;
  }
  close = gclose(saveFD);
  return true;
}

bool equals (SPLArray_char* first, SPLArray_char* second) {
  bool res_6;
  int i_6;
  
  if ((!((first->length) == (second->length)))) {
    return false;
  }
  i_6 = 0;
  while (true) {
    if (!(((i_6 < (first->length)) && ((first->arr[i_6]) == (second->arr[i_6]))))) {
      break;
    }
    i_6 = (i_6 + 1);
  }
  if ((i_6 >= (first->length))) {
    return true;
  } else {
    return false;
  }
  return res_6;
}

int setupDataConnection (int cmdFd_2, SPLArray_char* port_2) {
  int connectedDataFD_1;
  SPLArray_char* tmp_26;
  int sent_3;
  SPLArray_char* portMsg;
  bool datalistening;
  int dataFD_1;
  struct SocketAddressIP4* dataAddr;
  int copied_1;
  int closeData;
  bool bound;
  
  dataAddr = get_address4(NULL, port_2);
  if ((dataAddr == NULL)) {
    return (-1);
  }
  dataFD_1 = create_socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
  if ((dataFD_1 == (-1))) {
    free(dataAddr);
    
    return (-1);
  }
  bound = bind4(dataFD_1, dataAddr);
  if ((!bound)) {
    free(dataAddr);
    
    return (-1);
  }
  datalistening = glisten(dataFD_1, 10);
  if ((!datalistening)) {
    free(dataAddr);
    
    return (-1);
  }
  if ((((port_2->length) < 0) || ((port_2->length) > (65535 - 6)))) {
    free(dataAddr);
    
    return (-1);
  }
  tmp_26 = newSPLArray_char( (6 + (port_2->length)));
  portMsg = tmp_26;
  (portMsg->arr[0]) = ((char) 80);
  (portMsg->arr[1]) = ((char) 79);
  (portMsg->arr[2]) = ((char) 82);
  (portMsg->arr[3]) = ((char) 84);
  (portMsg->arr[4]) = ((char) 32);
  (portMsg->arr[5]) = ((char) 0);
  copied_1 = strcat(port_2, portMsg);
  sent_3 = tcp_send(cmdFd_2, portMsg, (portMsg->length));
  free(portMsg);
  
  if ((!(sent_3 == (portMsg->length)))) {
    free(dataAddr);
    
    return (-1);
  }
  connectedDataFD_1 = accept4(dataFD_1, dataAddr);
  free(dataAddr);
  
  closeData = gclose(dataFD_1);
  return connectedDataFD_1;
}

int strcat (SPLArray_char* str1_1, SPLArray_char* str2_1) {
  int res_7;
  int l2;
  int l1;
  int i_12;
  int copy_size;
  
  l1 = strlen(str1_1);
  l2 = strlen(str2_1);
  copy_size = ((str2_1->length) - l2);
  if ((copy_size > l1)) {
    copy_size = l1;
  }
  i_12 = 0;
  while (true) {
    if (!((i_12 < copy_size))) {
      break;
    }
    (str2_1->arr[(i_12 + l2)]) = (str1_1->arr[i_12]);
    i_12 = (i_12 + 1);
  }
  if (((l2 + copy_size) < (str2_1->length))) {
    (str2_1->arr[(l2 + copy_size)]) = ((char) 0);
  }
  return copy_size;
}

int strcmp (SPLArray_char* s1, SPLArray_char* s2) {
  int res_8;
  int i_14;
  
  i_14 = 0;
  while (true) {
    if (!((((i_14 < (s1->length)) && (i_14 < (s2->length))) && ((s1->arr[i_14]) == (s2->arr[i_14]))))) {
      break;
    }
    i_14 = (i_14 + 1);
  }
  if (((i_14 >= (s1->length)) && (i_14 >= (s2->length)))) {
    return 0;
  } else {
    if ((i_14 >= (s1->length))) {
      return (-1);
    } else {
      if ((i_14 >= (s2->length))) {
        return 1;
      } else {
        if (((s1->arr[i_14]) < (s2->arr[i_14]))) {
          return (-1);
        } else {
          return 1;
        }
      }
    }
  }
  return res_8;
}

SPLArray_char* strconcat (SPLArray_char* str1_2, SPLArray_char* str2_2) {
  SPLArray_char* res_9;
  SPLArray_char* tmp_27;
  int l2_1;
  int l1_1;
  int i_15;
  SPLArray_char* copy_1;
  
  l1_1 = strlen(str1_2);
  l2_1 = strlen(str2_2);
  
  tmp_27 = newSPLArray_char( (l1_1 + l2_1));
  copy_1 = tmp_27;
  i_15 = 0;
  while (true) {
    if (!((i_15 < l1_1))) {
      break;
    }
    (copy_1->arr[i_15]) = (str1_2->arr[i_15]);
    i_15 = (i_15 + 1);
  }
  while (true) {
    if (!((i_15 < (l1_1 + l2_1)))) {
      break;
    }
    (copy_1->arr[i_15]) = (str2_2->arr[(i_15 - l1_1)]);
    i_15 = (i_15 + 1);
  }
  return copy_1;
}

SPLArray_char* strdup (SPLArray_char* str_2) {
  SPLArray_char* res_10;
  SPLArray_char* tmp_28;
  int i_17;
  SPLArray_char* copy_2;
  
  tmp_28 = newSPLArray_char( (str_2->length));
  copy_2 = tmp_28;
  i_17 = 0;
  while (true) {
    if (!((i_17 < (str_2->length)))) {
      break;
    }
    (copy_2->arr[i_17]) = (str_2->arr[i_17]);
    i_17 = (i_17 + 1);
  }
  return copy_2;
}

int strlen (SPLArray_char* str_3) {
  int res_11;
  int i_18;
  
  i_18 = 0;
  while (true) {
    if (!(((i_18 < (str_3->length)) && (!((str_3->arr[i_18]) == ((char) 0)))))) {
      break;
    }
    i_18 = (i_18 + 1);
  }
  return i_18;
}

bool uploadFile (int cmdFd_3, int dataFD_2, SPLArray_char* filename_3) {
  bool success_9;
  SPLArray_int* tmp_34;
  SPLArray_char* tmp_33;
  SPLArray_int* tmp_32;
  SPLArray_char* tmp_31;
  SPLArray_char* tmp_30;
  SPLArray_char* tmp_29;
  int size_3;
  int sentData;
  int sent_4;
  SPLArray_char* sendMsg;
  int read;
  SPLArray_int* pleaseAccept_1;
  int opened;
  SPLArray_char* okMsg_2;
  int ok_2;
  int copied_2;
  int commandSize;
  int close_1;
  bool checked_2;
  SPLArray_char* buffer_7;
  SPLArray_int* acceptThese_2;
  
  size_3 = fileSize(filename_3);
  if (((size_3 < 0) || (size_3 > 65535))) {
    return false;
  }
  opened = gopen(filename_3, (O_CREAT | O_RDONLY));
  if ((opened < 0)) {
    return false;
  }
  tmp_29 = newSPLArray_char( size_3);
  buffer_7 = tmp_29;
  read = gread(opened, buffer_7);
  if ((read < 0)) {
    free(buffer_7);
    
    return false;
  }
  if ((((filename_3->length) < 0) || ((filename_3->length) > (65535 - 6)))) {
    free(buffer_7);
    
    return false;
  }
  commandSize = ((filename_3->length) + 6);
  tmp_30 = newSPLArray_char( commandSize);
  sendMsg = tmp_30;
  (sendMsg->arr[0]) = ((char) 83);
  (sendMsg->arr[1]) = ((char) 84);
  (sendMsg->arr[2]) = ((char) 79);
  (sendMsg->arr[3]) = ((char) 82);
  (sendMsg->arr[4]) = ((char) 32);
  (sendMsg->arr[5]) = ((char) 0);
  copied_2 = strcat(filename_3, sendMsg);
  sent_4 = tcp_send(cmdFd_3, sendMsg, commandSize);
  free(sendMsg);
  
  tmp_31 = newSPLArray_char( 4);
  okMsg_2 = tmp_31;
  ok_2 = tcp_recv(cmdFd_3, okMsg_2);
  tmp_32 = newSPLArray_int( 2);
  acceptThese_2 = tmp_32;
  (acceptThese_2->arr[0]) = 200;
  (acceptThese_2->arr[1]) = 150;
  checked_2 = checkServerResponse(okMsg_2, acceptThese_2);
  free(okMsg_2);
  
  free(acceptThese_2);
  
  if ((!checked_2)) {
    free(buffer_7);
    
    return false;
  }
  sentData = tcp_send(dataFD_2, buffer_7, size_3);
  tmp_33 = newSPLArray_char( 4);
  okMsg_2 = tmp_33;
  ok_2 = tcp_recv(cmdFd_3, okMsg_2);
  tmp_34 = newSPLArray_int( 3);
  pleaseAccept_1 = tmp_34;
  (pleaseAccept_1->arr[0]) = 200;
  (pleaseAccept_1->arr[1]) = 226;
  (pleaseAccept_1->arr[2]) = 250;
  checked_2 = checkServerResponse(okMsg_2, pleaseAccept_1);
  free(okMsg_2);
  
  free(pleaseAccept_1);
  
  free(buffer_7);
  
  if ((!checked_2)) {
    return false;
  }
  close_1 = gclose(opened);
  if ((sentData == size_3)) {
    return true;
  } else {
    return false;
  }
  return success_9;
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

