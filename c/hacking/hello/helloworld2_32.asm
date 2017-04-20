; This is just to check code works when making executable
;global _start
;_start:
; But we only want to assemble for shellcode, not make executable file

jmp short one ; jump down to the call at the end

two:
pop rcx
mov eax, 4
mov ebx, 1
mov edx, 15
int 0x80

mov eax, 1
mov ebx, 0
int 0x80

one:
call two  ; call back upwards to avoid null bytes
db "Hello, world!",0x0a,0x0d
