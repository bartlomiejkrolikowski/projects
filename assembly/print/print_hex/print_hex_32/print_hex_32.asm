; Bartlomiej Krolikowski

global print_hex_32

section .text
print_hex_32:
        mov eax, DWORD [esp + 4]        ; load the argument from the stack
        mov edx, eax                    ; copy to edx

        and eax, 0x0f0f0f0f             ; leave only lower nibbles in eax
                                        ; (lower digits from bytes)
        and edx, 0xf0f0f0f0             ; leave only upper nibbles in edx
                                        ; (lower digits from bytes)
        shr edx, 4                      ; shift digits to the right place in edx

        or eax, 0x30303030              ; convert to digit characters
        or edx, 0x30303030              ; convert to digit characters

        cmp al, '9'
        jle cmp1

        add al, 'a'-'9'-1

cmp1:
        xchg al, ah
        cmp al, '9'
        jle cmp2

        add al, 'a'-'9'-1

cmp2:
        xchg al, dh
        cmp al, '9'
        jle cmp3

        add al, 'a'-'9'-1

cmp3:
        xchg al, dl
        cmp al, '9'
        jle cmp4

        add al, 'a'-'9'-1
                                        ; to that place: moving the contents:
                                        ; al -> ah -> dh -> dl -> al
                                        ; with hex adjustments
cmp4:
        rol eax, 16
        xchg ax, dx                     ; put lower 4 digits in eax in display order
                                        ; (little endian)
                                        ; now, the upper 4 digits are in edx in normal order
                                        ; (big endian)
                                        ; they need to be adjusted to hex code and reversed

        cmp dl, '9'
        jle cmp5

        add dl, 'a'-'9'-1

cmp5:
        xchg dl, dh
        cmp dl, '9'
        jle cmp6

        add dl, 'a'-'9'-1

cmp6:
        rol edx, 16
        cmp dl, '9'
        jle cmp7

        add dl, 'a'-'9'-1

cmp7:
        xchg dl, dh
        cmp dl, '9'
        jle cmp8

        add dl, 'a'-'9'-1

cmp8:
        ror edx, 8
        xchg dl, dh                     ; set the middle digits in the proper order
        rol edx, 8
                                        ; now the order is correct
                                        ; digits may be displayed

        push ebx                        ; store ebx

        push eax                        ; save lower 4 digits
        push edx                        ; save upper 4 digits

        mov eax, 4
        xor ebx, ebx
        inc ebx
        mov ecx, esp
        mov edx, 8

        int 0x80                        ; write(1, esp, 8);

        add esp, 8                      ; remove the string from the stack

        pop ebx                         ; restore ebx
        ret                             ; finished
