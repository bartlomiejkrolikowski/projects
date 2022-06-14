; Bartlomiej Krolikowski

global print_bcd_32

section .text
print_bcd_32:
        mov eax, DWORD [esp+4]
        mov edx, eax

        and eax, 0x0f0f0f0f
        and edx, 0xf0f0f0f0
        shr edx, 4

        or eax, 0x30303030
        or edx, 0x30303030

        ; the order of characters: (eXx: XX,XX|Xh;Xl)
        ; edx: 7,5|3;1
        ; eax: 6,4|2;0

        xchg al, ah
        xchg al, dh
        xchg al, dl

        ; ah --> dh
        ; ^       |
        ; |       v
        ; al <-- dl

        ; edx: 7,5|2;3
        ; eax: 6,4|0;1

        rol eax, 16     ; eax: 0,1|6;4
        xchg ax, dx

        ; edx: 7,5|6;4
        ; eax: 0,1|2;3

        xchg dl, dh     ; edx: 7,5|4;6
        ror edx, 8      ; edx: 6,7|5;4
        xchg dl, dh     ; edx: 6,7|4;5
        ror edx, 16     ; edx: 4,5|6;7

        push ebx

        push eax
        push edx

        ; stack:
        ; eax: 33 22 11 00
        ; edx: 77 66 55 44
        ; (little endian)

        mov eax, 4
        xor ebx, ebx
        inc ebx
        mov ecx, esp
        mov edx, 8

        int 0x80

        add esp, 8

        pop ebx
        ret
