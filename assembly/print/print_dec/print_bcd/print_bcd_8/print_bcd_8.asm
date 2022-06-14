; Bartlomiej Krolikowski

global print_bcd_8

section .text
print_bcd_8:
        mov al, BYTE [esp + 4]  ; ax: xx 12

        mov ah, al              ; ax: 12 12
        and ah, 0x0f            ; ax: 02 12
        shr al, 4               ; ax: 02 01
        or ax, 0x3030           ; ax: ch2 ch1

        push ebx
        push ax                 ; stack: ch1, ch2, ebx

        xor ebx, ebx            ; ebx <- 1
        inc ebx
        mov edx, ebx            ; edx <- 2
        shl edx, 1
        mov eax, edx            ; eax <- 4
        shl eax, 1
        mov ecx, esp
        int 0x80

        inc esp
        inc esp
        pop ebx

        ret
