#ifndef UTIL_H
#define UTIL_H
#include <assert.h>
#include <stdio.h>

typedef char *string;
typedef char bool;

#define TRUE 1
#define FALSE 0

void *checked_malloc(int);
string String(char *);
typedef struct U_boolList_ *U_boolList;
struct U_boolList_ {bool head; U_boolList tail;};
U_boolList U_BoolList(bool head, U_boolList tail);
void printInstr(void *info);

#define DEBUG 0
#if DEBUG
#define DEBUG_PRINT(...) do{printf(__VA_ARGS__);}while(0);
#else
#define DEBUG_PRINT(...) do{}while(0);
#endif

#define tprintf(buf, ...) do{sprintf(buf, __VA_ARGS__); DEBUG_PRINT(__VA_ARGS__)DEBUG_PRINT("\n")}while(0);
#endif
