; Bartlomiej Krolikowski

global print_dec_16

section .text
print_dec_16:
	xor edx, edx

	mov ax, WORD [esp+4]
	mov cx, 10

	div cx
	shl edx, 16

	div cx
	xchg dl, dh
	shl edx, 8

	div cx
	xchg dl, dh

	div cl
	mov dl, ah

	or edx, 0x30303030
	or al, 0x30

	push ebx
	push edx
	dec esp
	mov BYTE [esp], al

	xor ebx, ebx
	inc ebx
	mov eax, ebx
	shl eax, 2
	mov ecx, esp
	mov edx, eax
	inc edx
	int 0x80

	inc esp
	pop edx
	pop ebx

	ret
