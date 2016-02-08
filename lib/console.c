#include <string.h>
#include <stdio.h>

/*
 * Preloaded Code
 */

typedef struct {
  int length;
  char arr[];
} SPLArray_char;

/*
 * Procedures
 */

int gputs(SPLArray_char* buffer) {
  bool null_terminated = false;
  for (int i = 0; i < buffer->length && !null_terminated; i++) {
    null_terminated = buffer->arr[i] != 0;
  }
  if (null_terminated) {
    return fputs(buffer->arr, stdout);
  } else {
    char str[buffer->length + 1]; //allocate on the stack for simplicity
    memcpy(str, buffer->arr, buffer->length);
    str[buffer->length] = 0;
    return fputs(str, stdout);
  }
}

int ggets(SPLArray_char* buffer) {
  if (fgets(buffer->arr, buffer->length, stdin) == NULL) {
    return -1;
  } else {
    return strnlen(buffer->arr, buffer->length);
  }
}
