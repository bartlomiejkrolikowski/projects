// stack.c
// Bartlomiej Krolikowski

#include <stack.h>
#include <stdio.h>
void delete_stack(stack_t *stack) {
   if (!stack) {
      // stack == 0
      return;
   }

   stack_node_t *psnt = to_psnt(stack->node);
   while (psnt) {
      stack_node_t *next_psnt = to_psnt(psnt->next);
      free(psnt);
      psnt = next_psnt;
   }

   free(stack);
}

void iterate(stack_node_t *in_psnt, void *out, void (*op)(stack_node_t*,void*)) {
   for (stack_node_t *psnt = in_psnt; psnt; psnt = to_psnt(psnt->next)) {
      op(psnt,out);
   }
}

//static void increment(void *counter) {
//   ((int)counter)++;
//}

int size(stack_t *stack) {
   if (!stack) {
      return 0;
   }

   int counter = 0;
   for (stack_node_t *psnt = to_psnt(stack->node); psnt; psnt = to_psnt(psnt->next)) {
      counter++;
   }
//   or: iterate(to_psnt(stack->node), &counter);

   return counter;
}

int top(stack_t *stack) {
   if (empty(stack)) {
      return 0;
   }

   return to_psnt(stack->node)->value;
}

int pop(stack_t *stack) {
   if (empty(stack)) {
      return 0;
   }

   stack_node_t *node = to_psnt(stack->node);
   int value = node->value;
   stack->node = node->next;

   free(node);
   return value;
}

void push(stack_t *stack, int value) {
   if (!stack) {
      return;
   }

   stack_node_t *node = to_psnt(malloc(sizeof(stack_node_t)));
   node->value = value;
   node->next = stack->node;
   stack->node = node;
}
