; Bartlomiej Krolikowski

global print_bcd_16

section .text
print_bcd_16:
                                ; order of number's digits: (0 - no digit, x - unknown, positive - indicates the order)
        mov ax, WORD [esp+4]    ; eax: xx xx 12 34

        shl eax, 8              ; eax: xx 12 34 00
        mov al, ah              ; eax: xx 12 34 34
        and ah, 0x0f            ; eax: xx 12 04 34
        shr al, 4               ; eax: xx 12 04 03
        rol eax, 16             ; eax: 04 03 xx 12
        mov ah, al              ; eax: 04 03 12 12
        and ah, 0xf             ; eax: 04 03 02 12
        shr al, 4               ; eax: 04 03 02 01

        or eax, 0x30303030      ; eax: ch4 ch3 ch2 ch1

        push ebx

        push eax
        ; esp -> ch1 ch2 ch3 ch4

        mov eax, 4
        xor ebx, ebx
        inc ebx
        mov ecx, esp
        mov edx, eax
        int 0x80

        pop ebx
        pop ebx

        ret
