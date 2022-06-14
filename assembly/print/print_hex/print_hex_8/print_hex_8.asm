; Bartlomiej Krolikowski

global print_hex_8

section .text
print_hex_8:
        movzx ax, BYTE [esp + 4]        ; load the argument from the stack
        ror ax, 4                       ; swap and split nibbles of al, storing it in different halves of ax
        shr ah, 4                       ; shift the digit in ah to the correct place (currently it is in the upper nibble)

        or ax, 0x3030                   ; convert to decimal digit characters - or is here like add,
                                        ; because '1' in the arguments do not overlap:
                                        ;       0x3030  =       00110000 00110000
                                        ;       0x0<c1>0<c2> =  0000<c1> 0000<c2>
                                        ; or ------------------------------------
                                        ;       0x3<c1>3<c2> =  0011<c1> 0011<c2>
                                        ; and it may be faster than addition

        cmp al, '9'                     ; check if the or is enough
        jle cmp_ah                      ; yes: another comparison

        add al, 'a'-'9'-1               ; no: repair to get a hex digit

cmp_ah:
        cmp ah, '9'                     ; check if the or is enough
        jle end                         ; yes: display it now

        add ah, 'a'-'9'-1               ; no: repair to get a hex digit

end:
        push ebx                        ; store ebx

        push ax                 ; store the result to display it

        mov eax, 4
        xor ebx, ebx
        inc ebx
        mov ecx, esp
        mov edx, 2

        int 0x80                        ; write(1, esp, 1);

        pop ax

        pop ebx                         ; restore ebx
        ret                             ; finished
