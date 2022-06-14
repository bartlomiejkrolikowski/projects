global main

extern malloc
extern free

section .text
main:
	mov eax, 10
	push eax

	call malloc

	mov edx, DWORD [hello]
	mov DWORD [eax], edx

	mov edx, DWORD [hello+4]
	mov DWORD [eax+4], edx

	mov DWORD [esp], eax

	mov ecx, eax
	mov eax, 4
	mov ebx, 1
	mov edx, DWORD [hellolen]
	int 0x80

	call free

	pop eax
	ret

section .data
hello:
	db 'Hello!', 0xa, 0
hellolen:
	dd $-hello
