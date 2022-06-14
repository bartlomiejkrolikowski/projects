; Bartlomiej Krolikowski
; analogous to 8-bit version

global print_hex_16

section .text
print_hex_16:
	push ebx
	xor eax, eax

	mov dx, WORD [esp+8]
	xor ecx, ecx

loop:
	mov ax, dx
	and ax, 0x0f0f

	cmp al, 10
	jge hex_l

	add al, '0'
	jmp next_l

hex_l:
	add al, 'a'-10

next_l:
	cmp ah, 10
	jge hex_h

	add ah, '0'
	jmp next_h

hex_h:
	add ah, 'a'-10

next_h:
	shl eax, 8
	shr ax, 8

	cmp cl, ch
	jne end

	mov ebx, eax
	shr dx, 4
	inc cl
	jmp loop

end:
	shl eax, 8
	or ebx, eax

	xchg bl, bh
	rol ebx, 16
	xchg bl, bh

	push ebx

	mov eax, 4
	xor ebx, ebx
	inc ebx
	mov ecx, esp
	mov edx, 4
	int 0x80

	pop ebx
	pop ebx

	ret
