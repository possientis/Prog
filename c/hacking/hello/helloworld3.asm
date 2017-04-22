; This is just to check code works when making executable
;global _start
;_start:
; But we only want to assemble for shellcode, not make executable file

; BEAUTIFUL: the shellcode has no null byte !!!



; helloworld3.o:     file format elf64-x86-64
; 
; 
; Disassembly of section .text:
; 
; 0000000000000000 <.text>:
;    0:	eb 1c                	jmp    0x1e
;    2:	5e                   	pop    rsi
;    3:	48 31 c0             	xor    rax,rax
;    6:	ff c0                	inc    eax
;    8:	48 31 ff             	xor    rdi,rdi
;    b:	ff c7                	inc    edi
;    d:	48 31 d2             	xor    rdx,rdx
;   10:	b2 0f                	mov    dl,0xf
;   12:	0f 05                	syscall 
;   14:	48 31 c0             	xor    rax,rax
;   17:	b0 3c                	mov    al,0x3c
;   19:	48 31 ff             	xor    rdi,rdi
;   1c:	0f 05                	syscall 
;   1e:	e8 df ff ff ff       	call   0x2
;   23:	48                   	rex.W
;   24:	65 6c                	gs ins BYTE PTR es:[rdi],dx
;   26:	6c                   	ins    BYTE PTR es:[rdi],dx
;   27:	6f                   	outs   dx,DWORD PTR ds:[rsi]
;   28:	2c 20                	sub    al,0x20
;   2a:	77 6f                	ja     0x9b
;   2c:	72 6c                	jb     0x9a
;   2e:	64 21 0a             	and    DWORD PTR fs:[rdx],ecx
;   31:	0d                   	.byte 0xd


jmp short one ; jump down to the call at the end (short jmp -> no null byte)

two:
pop rsi

xor rax, rax
inc eax       ; mov rax, 1 ... but avoiding null bytes

xor rdi, rdi  ; mov rdi, 1 ... but avoiding null bytes
inc edi

xor rdx, rdx  ; mov rdx, 15 ... but avoiding null bytes
mov dl, 15

syscall

xor rax, rax
mov al, 60

xor rdi, rdi

syscall

one:
call two  ; call back upwards to avoid null bytes
db "Hello, world!",0x0a,0x0d
