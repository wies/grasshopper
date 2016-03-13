/*
 * Includes
 */
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <assert.h>

/*
 * Preloaded Code
 */

typedef struct {
  int length;
  int arr[];
} SPLArray_int;

typedef struct {
  int length;
  bool arr[];
} SPLArray_bool;

typedef struct {
  int length;
  char arr[];
} SPLArray_char;

typedef struct {
  int length;
  void* arr[];
} SPLArray_generic;

/*
 * Procedures
 */
int gclose (int fd);
int gopen (SPLArray_char* pathname, int flags);
int gread (int fd_2, SPLArray_char* buffer);
int greadOffset (int fd_3, SPLArray_char* buffer_1, int offset);
int gwrite (int fd_4, SPLArray_char* buffer_2);
int gwrite2 (int fd_4, SPLArray_char* buffer_2, int size);
int fileSize (SPLArray_char* pathname);
