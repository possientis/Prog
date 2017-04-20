; This is just to check code works when making executable
;global _start
;_start:
; But we only want to assemble for shellcode, not make executable file

; PROBLEM: we have managed to eliminate null bytes due to jumps, 
; but we still have null bytes from low 32 bits operands.

;helloworld2.o:     file format elf64-x86-64

;Disassembly of section .text:

;0000000000000000 <.text>:
;   0:	eb 28                	jmp    0x2a
;   2:	5e                   	pop    rsi
;   3:	48 c7 c0 01 00 00 00 	mov    rax,0x1
;   a:	48 c7 c7 01 00 00 00 	mov    rdi,0x1
;  11:	48 c7 c2 0f 00 00 00 	mov    rdx,0xf
;  18:	0f 05                	syscall 
;  1a:	48 c7 c0 3c 00 00 00 	mov    rax,0x3c
;  21:	48 c7 c7 00 00 00 00 	mov    rdi,0x0
;  28:	0f 05                	syscall 
;  2a:	e8 d3 ff ff ff       	call   0x2
;  2f:	48                   	rex.W
;  30:	65 6c                	gs ins BYTE PTR es:[rdi],dx
;  32:	6c                   	ins    BYTE PTR es:[rdi],dx
;  33:	6f                   	outs   dx,DWORD PTR ds:[rsi]
;  34:	2c 20                	sub    al,0x20
;  36:	77 6f                	ja     0xa7
;  38:	72 6c                	jb     0xa6
;  3a:	64 21 0a             	and    DWORD PTR fs:[rdx],ecx
;  3d:	0d                   	.byte 0xd

jmp short one ; jump down to the call at the end

two:
pop rsi
mov rax, 1
mov rdi, 1
mov rdx, 15
syscall

mov rax, 60
mov rdi, 0
syscall

one:
call two  ; call back upwards to avoid null bytes
db "Hello, world!",0x0a,0x0d
