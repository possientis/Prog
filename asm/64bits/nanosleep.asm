section .data
        delay dq 5, 500000000 ; struct timespec { tv_sec = 5, tv+nsec = 500000000 }

section .text
        global _start

_start:

        mov rax, 35     ; sys_nanosleep
        mov rdi, delay  ; first argument pointer to struct timespec
        mov rsi, 0      ; second argument, NULL pointer to struct timespec
        syscall

        mov rax, 60
        mov rdi, 0
        syscall
