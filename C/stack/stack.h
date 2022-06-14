// stack.h
// Bartlomiej Krolikowski

#ifndef __stack_h__
#define __stack_h__

#include <stdlib.h>

typedef struct {
   int value;
   void *next;
} stack_node_t;

typedef struct {
   stack_node_t *node;
} stack_t;

static stack_node_t *to_psnt(void *node) {
   return node;
}

static stack_t *new_stack() {
   stack_t *stack = malloc(sizeof(stack_t));
   stack->node = 0;
   return stack;
}

void delete_stack(stack_t*);

static int empty(stack_t *stack) {
   if (!stack || !stack->node) {
      return 1;
   } else {
      return 0;
   }
}

void iterate(stack_node_t*,void*,void (*)(stack_node_t*,void*));
int size(stack_t*);
int top(stack_t*);
int pop(stack_t*);
void push(stack_t*,int);

#endif
