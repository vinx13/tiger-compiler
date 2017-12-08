#include <stdio.h>
#include <stdlib.h>
#include "stack.h"
#include "util.h"                                
                                    
Stack *Stack_Init() {        
    Stack *S = checked_malloc(sizeof(*S));
    S->size = 0;
    return S;
}

void Stack_Destroy(Stack *S) {
    free(S);
}

void *Stack_Top(Stack *S) {
    if (S->size == 0) {
        fprintf(stderr, "Error: stack empty\n");
        return NULL;
    } 

    return S->data[S->size-1];
}

void Stack_Push(Stack *S, void *d){
    assert(S->size < STACK_MAX);
    S->data[S->size++] = d;
}

void Stack_Pop(Stack *S) {
    assert(S->size >0);
    S->size--;
}

bool Stack_Empty(Stack *S) {
    return S->size == 0;
}

