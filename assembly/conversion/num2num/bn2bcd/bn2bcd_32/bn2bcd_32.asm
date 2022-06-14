; Bartlomiej Krolikowski

; assumption: result in bcd can fit in 32-bit register
;       (max 8 digits), otherwise the result is truncated
;       to the first 8 digits

global bn2bcd_32

section .text
bn2bcd_32:                      ; conversion of 8-digit number (in decimal) to BCD (32-bit input and result)
        mov edx, DWORD [esp+4]
        xor eax, eax
        mov ecx, 32

.loop:
        shl edx, 1
        adc al, al      ; shift the lowest (0) byte
        daa
        xchg al, ah
        adc al, al      ; shift byte 1
        daa
        xchg al, ah
        pushf
        rol eax, 16     ; swap the highest and the lowest bytes
        popf
        adc al, al      ; shift byte 2
        daa
        xchg al, ah
        adc al, al      ; shift byte 3
        daa
        xchg al, ah
        rol eax, 16     ; move the bytes to their place
        loop .loop

        ret             ; result in eax
