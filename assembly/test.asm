; Bartlomiej Krolikowski

global _start

extern print_bcd_8
extern bn2bcd_long

section .text
_start:
	push DWORD [result_len]
	push result
	push DWORD [number_len]
	push number

	; arguments - reversed relative to the order of input

	call bn2bcd_long		; convert a binary number to binary-coded decimal

;	mov DWORD [esp], eax

	add esp, 16

	push result
	push DWORD [result_len]

	call print_bcd_long		; print in bcd

	mov eax, 4
	xor ebx, ebx
	inc ebx
	mov ecx, newline
	xor edx, edx
	inc edx
	int 0x80			; print newline

	xor eax, eax
	inc eax
	xor ebx, ebx
	int 0x80			; exit

print_bcd_long:
	push edi
	push esi

	mov edi, DWORD [esp+12]		; first argument: buffer length
	mov esi, DWORD [esp+16]		; second argument: pointer to the buffer

	dec esp

.loop:
	dec edi

	mov al, BYTE [esi+edi]
	mov BYTE [esp], al		; passing subsequent bytes as arguments on the stack

	call print_bcd_8		; print two digits

	test edi, edi			; check if finished (if we used the lowest byte)
	jnz .loop

	inc esp

	pop esi
	pop edi

	ret

section .data
number:			; 2^64
	dd 0
	dd 0
	db 1

number_len:
	dd $-number	; here: 9

newline:
	db 0x0a

result:
times 18	db 15

result_len:
	dd $-result
