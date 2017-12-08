/*
 * util.c - commonly used utility functions.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "temp.h"
#include "assem.h"
#include "frame.h"
#include "symbol.h"

void *checked_malloc(int len)
{void *p = malloc(len);
 if (!p) {
    fprintf(stderr,"\nRan out of memory!\n");
    exit(1);
 }
 return p;
}

string String(char *s)
{string p = checked_malloc(strlen(s)+1);
 strcpy(p,s);
 return p;
}

U_boolList U_BoolList(bool head, U_boolList tail)
{ U_boolList list = checked_malloc(sizeof(*list));
  list->head = head;
  list->tail = tail;
  return list;
}

void printInstr(void *info) {
#if DEBUG
  AS_instr instr = (AS_instr)info;
  AS_print(stdout, instr, Temp_layerMap(F_regTempMap(), Temp_name()));
#endif
}

