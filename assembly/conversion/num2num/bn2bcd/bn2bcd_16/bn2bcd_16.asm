; Bartlomiej Krolikowski

global bn2bcd_16

section .text
bn2bcd_16:                      ; conversion of 4-digit number (in decimal) to BCD (16-bit input and result)
        mov dx, WORD [esp + 4]
        xor eax, eax
        mov ecx, 16     ; 16 iterations: 16 bits

.loop:
        shl dx, 1
        adc al, al
        daa             ; daa sets CF if overflow in BCD happens
        xchg al, ah
        adc al, al      ; taking care of the overflow while shifting left
        daa
        xchg al, ah
        loop .loop

        ret             ; result in eax (ax)
