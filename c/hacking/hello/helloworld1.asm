; Using call just before data, so address of data
; is pushed onto the stack. This creates standalone
; code which is also position independent

; PROBLEM: the shell code resulting from this will
; contain many null bytes, which does not lend 
; itself to communication as strings. 

;helloworld1.o:     file format elf64-x86-64

;Disassembly of section .text:

;0000000000000000 <.text>:
;   0:	e8 0f 00 00 00       	call   0x14
;   5:	48                   	rex.W
;   6:	65 6c                	gs ins BYTE PTR es:[rdi],dx
;   8:	6c                   	ins    BYTE PTR es:[rdi],dx
;   9:	6f                   	outs   dx,DWORD PTR ds:[rsi]
;   a:	2c 20                	sub    al,0x20
;   c:	77 6f                	ja     0x7d
;   e:	72 6c                	jb     0x7c
;  10:	64 21 0a             	and    DWORD PTR fs:[rdx],ecx
;  13:	0d 5e 48 c7 c0       	or     eax,0xc0c7485e
;  18:	01 00                	add    DWORD PTR [rax],eax
;  1a:	00 00                	add    BYTE PTR [rax],al
;  1c:	48 c7 c7 01 00 00 00 	mov    rdi,0x1
;  23:	48 c7 c2 0f 00 00 00 	mov    rdx,0xf
;  2a:	0f 05                	syscall 
;  2c:	48 c7 c0 3c 00 00 00 	mov    rax,0x3c
;  33:	48 c7 c7 00 00 00 00 	mov    rdi,0x0
;  3a:	0f 05                	syscall


 
;global _start
;_start:
call mark_below
db "Hello, world!", 0x0a,0x0d

mark_below:
pop rsi
mov rax, 1
mov rdi, 1
mov rdx, 15
syscall

mov rax, 60
mov rdi, 0
syscall


 
