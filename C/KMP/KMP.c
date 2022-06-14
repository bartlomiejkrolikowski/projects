// KMP.c
// Bartlomiej Krolikowski

#include<stdio.h>

#define NEXT_SEARCH -1
#define TRUE 1
#define FALSE 0

// algorithm KMP for finding a pattern in a text in linear time O(n + m)
// n - length of the searched text
// m - length of the pattern
int main() {
   int index = 0, beginning_index, comparing_index, retraction_size, text_size, template_size;
   char is_partly_matching = FALSE, is_not_completely_matching = TRUE;

   printf("Give the lenght of the searched text and the length of the pattern (at least 1) :\n");
   scanf("%d %d", &text_size, &template_size);

   char text[ text_size + 1 ], template_string[ template_size + 1 ];
   int timi[ template_size ]; // template_internal_mismatch_index

   printf("Give the searched text and the pattern (space separates):\n");
   scanf("%s %s", text, template_string);

   // index == 0
   while ( index < template_size ) {
      timi[ index++ ] = NEXT_SEARCH;
   }

   // initiation of timi

   index = 1;
   while (index < template_size) {
      if ( is_partly_matching ) {
         if ( template_string[ index ] == template_string[ comparing_index ] ) {
            timi[ index ] = timi[ comparing_index ] + beginning_index;
            ++comparing_index;

         }
         else {
            timi[ index ] = beginning_index;

            retraction_size = timi[ comparing_index ];
            if ( retraction_size == NEXT_SEARCH ) {
               is_partly_matching = FALSE;
            }

            else {
               is_partly_matching = TRUE;
               beginning_index += retraction_size - 1;
               comparing_index -= retraction_size - 1;

            }

            --index;

         }

      }
      else {
         if ( template_string[ index ] == template_string[0] ) {
            is_partly_matching = TRUE;

            beginning_index = index;
            comparing_index = 1;

         }

      }

      ++index;

   }

   // timi is ready
   // start search

   index = 0;
   is_partly_matching = FALSE;
   while ( index < text_size && is_not_completely_matching ) {
      if ( is_partly_matching ) {
         if ( comparing_index == template_size ) {
            is_not_completely_matching = FALSE;

         }
         else {
            if ( text[ index ] != template_string[ comparing_index ] ) {
               if ( timi[ comparing_index ] == NEXT_SEARCH ) {
                  is_partly_matching = FALSE;

               }
               else {
                  comparing_index -= timi[ comparing_index ];

               }

               --index;

            }
            else {
               ++comparing_index;

            }

         }

      }
      else {
         if ( text[ index ] == template_string[0] ) {
            is_partly_matching = TRUE;
            comparing_index = 1;

         }

      }

      ++index;

   }

   if ( is_not_completely_matching && comparing_index < template_size) {
      printf("Pattern not found.\n");

   }
   else {
      printf("First occurrence of the pattern on positions between (%d, %d).\n", index - template_size, index - 1);

   }

   return 0;

}
