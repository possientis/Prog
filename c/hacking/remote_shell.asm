section .text
global _start
_start:

  ; sockfd = socket(PF_INET, SOCK_STREAM, 0)
  mov     rdi, 2    ; PF_INET = 2
  mov     rsi, 1    ; SOCK_STREAM = 1
  mov     rdx, 0    ; 
  mov     rax, 41   ; sys_socket 64 bits
  syscall
  mov     rdi, rax  ; saving return code 
  
  mov rax, 60
  syscall
