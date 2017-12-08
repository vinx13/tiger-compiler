#define STACK_MAX 10000
#include "util.h"

typedef struct StackTag {       
    void *data[STACK_MAX];      
    int size;               
} Stack;                                       
                                
                                    
Stack *Stack_Init();

void Stack_Destroy(Stack *S);

void *Stack_Top(Stack *S);

void Stack_Push(Stack *S, void *d);

void Stack_Pop(Stack *S);

bool Stack_Empty(Stack *S);


