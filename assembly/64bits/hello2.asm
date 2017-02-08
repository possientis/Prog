      section .data
text  db "Hello World!",0x0a   ; string is not null terminated, using write

      section .text
      global _start 

_start:
      mov rax, 1      ; system call 1 write (0 read, 2 open, 3 close)
      mov rdi, 1      ; first agument for write, file descriptor (stdout) 
      mov rsi, text   ; second argument for write, buffer
      mov rdx, 13     ; third argument for write, size
      syscall         ; calling write

      mov rax, 0x3c   ; exit system call
      mov rdi, 0      ; first argument for exit
      syscall
