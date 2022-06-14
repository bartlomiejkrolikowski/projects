; Bartlomiej Krolikowski

global print_dec_8

section .text
print_dec_8:
        xor edx, edx

        movzx ax, BYTE [esp+4]  ; ax = [1]*100+[2]*10+[3]
        mov cx, 10
        div cx                  ; ax = [1]*10+[2] ; edx: 00 00 00 [3]
        shl edx, 16             ; edx: 00 [3] 00 00

        div cl                  ; ax: [2] [1]
        mov dx, ax              ; edx: 00 [3] [2] [1]

        or edx, 0x00303030

        push ebx
        push edx

        xor ebx, ebx
        inc ebx
        mov ecx, esp
        xor edx, edx
        mov dl, 3
        mov eax, edx
        inc eax
        int 0x80

        pop edx
        pop ebx

        ret
