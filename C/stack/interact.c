// interact.c
// Bartlomiej Krolikowski

#include <stdio.h>
#include <stdlib.h>
#include <stack.h>

int main() {
   stack_t *stack = new_stack();

   for (int c = getchar(); c != EOF; c = getchar()) {
      if (c == 'e') {
         if (empty(stack)) {
            printf("true");
         } else {
            printf("false");
         }
      } else if (c == 's') {
         printf("%d", size(stack));
      } else if (c == 't') {
         printf("%d", top(stack));
      } else if (c == '-') {
         printf("%d", pop(stack));
      } else if (c == '+') {
         int value;
         scanf("%d", &value);
         push(stack, value);
      }
      printf("\n");
   }

   delete_stack(stack);

   return 0;
}
