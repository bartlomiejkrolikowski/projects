; Bartlomiej Krolikowski

global bn2bcd_8

section .text
bn2bcd_8:                       ; conversion of 2-digit number (in decimal) to BCD (8-bit input and result)
        mov dl, BYTE [esp+4]
        mov ecx, 8
        xor eax, eax

.loop:                  ; converting a number by shifting it bit by bit to decimal register
        shl dl, 1
        adc al, al
        daa
        loop .loop

        ret             ; result in al
