// TMParser.c
// Bartlomiej Krolikowski

#include <stdio.h>
#include <stack.h>

typedef struct {
   int state;
   int letter;
   char move;
} newstate_t;

static int states, letters;
static newstate_t *newstates;

static newstate_t *newstate_at(int state, int letter) {
   return newstates + state * (letters+1) + letter;
}

void print_content(stack_node_t *psnt, void *out) {
   printf("%d ", psnt->value);
}

int main(int argc, char **argv) {
   stack_t *left = new_stack();
   stack_t *right = new_stack();
   int state = 0;
   int letter = 0;
   int input_len = 0;
   char move = '-';
   char printing = (argc > 1);

   scanf("%d", &states);
   scanf("%d", &letters);
   scanf("%d", &input_len);

   newstates = malloc(states * (letters+1) * sizeof(newstate_t));

   for (int i=0; i < states * (letters+1); i++) {
      newstates[i] = (newstate_t){-1,0,'-'};
   }

   while (input_len) {
      int next_st, next_let, notempty = scanf("%d, %d - %d, %d, %c", &state, &letter, &next_st, &next_let, &move);

      if (!notempty) {
         break;
      }

      if (state < 0 || state >= states) {
         fprintf(stderr, "state out of range\n");
         return -1;
      }

      if (letter < 0 || letter > letters) {
         fprintf(stderr, "letter out of range\n");
         return -1;
      }

      if (next_let < 0 || next_let > letters) {
         fprintf(stderr, "next letter out of range\n");
         return -1;
      }

      if (move != '<' && move != '-' && move != '>') {
         fprintf(stderr, "wrong move\n");
         return -1;
      }

      *newstate_at(state, letter) = (newstate_t){next_st, next_let, move};

      input_len--;
   }

   for (int notempty = scanf("%d", &letter); notempty && letter; notempty = scanf("%d", &letter)) {
      if (letter < 0 || letter > letters) {
         fprintf(stderr, "letter out of range\n");
         return -1;
      }

      push(left, letter);
   }

   for (int st_empty = empty(left); !st_empty; st_empty = empty(left)) {
      push(right, pop(left));
   }

   state = 0;
   letter = pop(right); // empty -> 0

   while (state >=0 && state < states) {
      if (printing) {
         printf("--\nright: ");
         iterate(right->node, 0, print_content);
         printf("\ncurrent: %d\nleft: ", letter);
         iterate(left->node, 0, print_content);
         printf("\n");
      }

      newstate_t next = *newstate_at(state, letter);
      state = next.state;
      letter = next.letter;

      if (next.move == '<') {
         push(right, letter);
         letter = pop(left); // empty -> 0
      } else if (next.move == '>') {
         push(left, letter);
         letter = pop(right); // empty -> 0
      }
   }

   printf("--end:--\nright: ");
   iterate(right->node, 0, print_content);
   printf("\ncurrent: %d\nleft: ", letter);
   iterate(left->node, 0, print_content);
   printf("\n");

   return 0;
}
