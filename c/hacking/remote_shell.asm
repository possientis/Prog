section .text
global _start
_start:

  ; sockfd = socket(PF_INET, SOCK_STREAM, 0)
  mov     rdi, 2            ; PF_INET = 2
  mov     rsi, 1            ; SOCK_STREAM = 1
  mov     rdx, 0         
  mov     rax, 41           ; sys_socket 64 bits
  syscall
  mov     r8, rax           ; saving sockd for later

  ; bind(sockfd, &host_addr, 16)
  mov     rbx, 0xe02e0002   ; AF_INET = 2 (word) port = 12000 (0x2ee0 big endian)  
                            ; IP = 0 (dword)
  push    rbx               ; 0x02  0x00  0x2e  0xe0  0x00  0x00  0x00  0x00  
  mov     rdi, r8           ; sockfd is first argument
  mov     rsi, rsp          ; &host_addr second argument 
  mov     rdx, 16           ; sizeof(struct sockaddr)(only first 8 matter here)
  mov     rax, 49           ; sys_bind 64 bits
  syscall

  ; listen(sockfd, 4)
  mov     rdi, r8           ; sockfd is first argument
  mov     rsi,  4           ; second argument
  mov     rax, 50           ; sys_listen 64 bits
  syscall

  mov     rdi, rax          ; TEMP, expecting 0 return value
  
  
  mov rax, 60
  syscall
