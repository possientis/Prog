section .bss
        BUFFLEN equ 16      ; we read the file 16 bytes at a time
        Buff: resb BUFFLEN  ; text buffer

section .data
        HexStr: db " 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00",10
        HEXLEN equ $-HexStr

        Digits: db "0123456789abcdef"

section .text
global _start

_start:

        nop     ; debugger happy

Read:
        mov rax,  0       ; sys_read for 64 bits ABI
        mov rdi,  0       ; stdin
        mov rsi,  Buff    ; read buffer
        mov rdx,  BUFFLEN ; number of bytes to be read per pass
        syscall

        mov rbp, rax      ; save return value
        cmp rax, 0        ; EOF?
        je  Exit          


        mov rsi,  Buff    ; preparing to read the 16 bytes (or whatever was read)
        mov rdi,  HexStr  
        xor rcx,  rcx     ; counter = 0

Scan:
        xor rax,  rax     ; used to read current byte

        mov rdx,  rcx     ; multiplying counter by 3 for position in output
        shl rdx,  1       ; x 2
        add rdx,  rcx     ; x 3 -> rdx

        mov al,   byte [rsi+rcx]      ; take byte from read buffer
        mov rbx,  rax                 ; duplicate for second nimble

        and rax,  0x0f                ; keep low nibble
        mov al,   byte [Digits+rax]   ; get corresponding hex digit
        mov byte  [HexStr+rdx+2], al  ; write to output string

        shr bl,   4                   ; align high nibble
        and rbx,  0xf                 ; mask out everything else
        mov bl,   byte [Digits+rbx]   ; get corresponding hex digit
        mov byte  [HexStr+rdx+1], bl  ; write to output string

        inc rcx           ; counter++
        cmp rcx, rbp      ; if counter < num bytes then scan next byte
        jb Scan

        mov rax,  1       ; sys_write for 64 bits ABI
        mov rdi,  1       ; stdout   
        mov rsi,  HexStr
        mov rdx,  HEXLEN
        syscall
        jmp Read          ; read next batch of 16 bytes

Exit:
        mov rax, 60       ; sys_exit for 64 bits ABI
        xor rdi, rdi      ; return value = 0
        syscall

        
