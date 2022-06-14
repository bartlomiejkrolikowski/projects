; Bartlomiej Krolikowski

; converts n-byte number stored in a buffer starting at the address pn
; to BCD, writing the result in b-byte buffer at the address pb
;
; all in little endian (most significant byte at the end)
;
; arguments:
; 1.: pn        DWORD
; 2.: n         DWORD
; 3.: pb        DWORD
; 4.: b         DWORD
;
; complexity:
; 4 * b * n     (number of bits of input number * number of bytes of the output)

global bn2bcd_long

section .text
bn2bcd_long:
        push ebp
        mov ebp, esp

        push ebx
        push esi
        push edi

        mov ebx, DWORD [ebp+16]         ; in ebx - beginning of the output buffer  (lowest byte)

        mov ecx, DWORD [ebp+20]         ; for the time of zeroing: in ecx - number of output buffer bytes
        mov edx, ecx                    ; in edx - number of output buffer bytes
        xor eax, eax

        dec ebx                         ; number in ebx is 1 too big at the moment

zero:                                   ; zero the output buffer
        mov BYTE [ebx+ecx], al
        loop zero

        inc ebx                         ; restore ebx

        mov esi, DWORD [ebp+8]
        mov ecx, DWORD [ebp+12]         ; in ecx - number fo bytes of the input number = number of outer loop iterations
        lea esi, [esi+ecx-1]            ; in esi - highest not processed byte of the input number

loop_n:
        xor al, al
        shl eax, 16                     ; in the third byte of eax - number of middle loop iterations so far (stop when 8 = size of a byte)
        mov ah, BYTE [esi]              ; in ah - currently processed byte
        mov DWORD [ebp+20], ecx         ; in place of the last argument - copy of ecx state from the outer loop

loop_shl:
        mov ecx, edx                    ; in ecx (inside the middle loop) - number of bytes of the output buffer = number of inner loop iterations
        mov edi, ebx                    ; in edi - beginning of the output buffer  (lowest byte)

        shl ah, 1                       ; get the highest byte

loop_b:
        mov al, BYTE [edi]
        adc al, al
        daa
        mov BYTE [edi], al              ; decimal multi-byte bit shift with carry (initial carry - carry bit from ah)

        inc edi                         ; move to the next (higher) byte
        loop loop_b

        ; end of loop_b

        rol eax, 16                     ; swap the halves of eax
        inc al
        mov ecx, eax                    ; copy to ecx (to swap halves again there)
        rol ecx, 16

        cmp al, 8
        mov eax, ecx                    ; before jumping restore al
        jl loop_shl                     ; repeat loop_shl until all bits will be transferred

        ; end of loop_shl

        mov ecx, DWORD [ebp+20]         ; restore the outer loop counter
        dec esi
        loop loop_n

        ; end of loop_n

        pop edi
        pop esi
        pop ebx

        mov esp, ebp
        pop ebp                         ; restore values of registers

        ret
