%macro exit 0         ; 0 argument
    mov rax, SYS_EXIT
    mov rdi, 15
    syscall
%endmacro

%macro exitcode 1     ; 1 argument
    mov rax, SYS_EXIT
    mov rdi, %1       ; first argument referred to as %1
    syscall
%endmacro

%macro freeze 0
%%loop:           ; macro label, gets its unique name upon macro expansion
  jmp %%loop
%endmacro

STDIN     equ 0
STDOUT    equ 1
STDERR    equ 2

SYS_READ  equ 0
SYS_WRITE equ 1
SYS_EXIT  equ 60


