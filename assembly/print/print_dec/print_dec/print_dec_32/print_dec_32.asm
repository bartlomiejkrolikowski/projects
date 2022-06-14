; Bartlomiej Krolikowski

global print_dec_32

section .text
print_dec_32:
	push ebx

	xor edx, edx
	mov eax, DWORD [esp+8]

	mov ecx, 10000
	div ecx

	mov ebx, eax
	mov eax, edx
	xor edx, edx

	shl ecx, 16
	mov cx, 10
	div cx
	shl edx, 16

	div cx
	xchg dl, dh
	shl edx, 8

	div cl
	mov dx, ax

	or edx, 0x30303030

	push edx

	mov edx, ebx
	shr edx, 16
	mov eax, ebx

	rol ecx, 16
	div cx

	mov ebx, eax
	mov eax, edx
	xor edx, edx

	shr ecx, 16
	div cx
	shl edx, 16

	div cx
	xchg dl, dh
	shl edx, 8

	div cl
	mov dx, ax

	or edx, 0x30303030

	push edx

	mov eax, ebx
	div cl

	or ax, 0x3030

	push ax

	xor ebx, ebx
	inc ebx
	mov ecx, esp
	mov eax, ebx
	inc eax
	mov edx, eax
	shl edx, 2
	or edx, eax
	shl eax, 1
	int 0x80

	add esp, 10
	pop ebx

	ret
