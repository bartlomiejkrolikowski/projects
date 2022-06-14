; Bartlomiej Krolikowski

global _start

section .text
_start:
	mov rax, 1
	mov rdi, 1
	mov rsi, hello64
	mov rdx, QWORD [helloLEN]
	syscall

	mov rax, 60
	mov rdi, 0
	syscall

section .data
hello64:
	db 'Hello World', 10

helloLEN:
	dq $-hello64
