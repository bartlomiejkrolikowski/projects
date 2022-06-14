; Bartlomiej Krolikowski

global _start

section .text
_start:
	; push ebp
	mov ebp, esp

	push 0x000a2164	; d!'\n''\0'
	push 0x6c726f57	; Worl
	push 0x206f6c6c	; llo' '
	push 0x6548	; He

	mov eax, 4
	mov ebx, 1
	mov ecx, esp
	mov edx, ebp
	sub edx, esp
	int 0x80

	mov eax, 1
	xor ebx, ebx
	int 0x80
