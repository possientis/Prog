section     .data
  ErrMsg    db    "Terminated with error.",10
  ERRLEN    equ   $-ErrMsg 

section     .bss
  MAXARGS   equ   10        ; maximum number of arguments supported
  ArgCount  resq  1         ; number of arguments passed to program
  ArgPtrs   resq  MAXARGS   ; table of pointers to arguments
  ArgLens   resq  MAXARGS   ; table of argument lengths

section     .text
global      _start

_start:

; get the number of arguments off the stack and validate it
  pop       rcx
  cmp       rcx,  MAXARGS
  ja        Error
  mov       [ArgCount], rcx
  
  mov       rdi,  [ArgCount]

; save arguments pointers
  xor       rdx,  rdx
SaveArgs:
  pop qword [ArgPtrs+8*rdx]
  inc       rdx
  cmp       rdx,  rcx
  jb        SaveArgs

; calculating lengths of arguments

  xor       rax,  rax                 ; al = 0 (we are searching for null byte)
  xor       rbx,  rbx
ScanOne:
  mov       rcx,  0x000000000000ffff  ; no more than 64k bytes 
  mov       rdi, [ArgPtrs+rbx*8]      ; address of string into rdi
  mov       rdx, rdi                  ; copy into rdx
  cld                                 ; clear direction flag (memory++)
  repne     scasb                     ; search byte == al in string at rdi
  jnz       Error                     ; REPNE SCASB ended without finding AL
  mov byte  [rdi-1], 10               ; Store EOL where the null byte used to be  
  sub       rdi, rdx                  ; 
  mov qword [ArgLens+8*rbx], rdi      ; saving length
  inc       rbx                       ; next argument 
  cmp       rbx, [ArgCount]
  jb        ScanOne

; display arguments
  xor       rbx, rbx
Show
  mov       rax, 1                    ; sys_write 64 bits
  mov       rdi, 1                    ; stdout
  mov       rsi, [ArgPtrs+8*rbx]      ; string address in rsi
  mov       rdx, [ArgLens+8*rbx]      ; length of string in rdx
  syscall
  inc       rbx
  cmp       rbx, [ArgCount]
  jb        Show

  jmp       Exit

Error:
  mov       rax,  1         ; sys_write 64 bytes 
  mov       rdi,  2         ; stderr
  mov       rsi,  ErrMsg 
  mov       rdx,  ERRLEN
  syscall
  mov       rdi, 255

Exit:
  mov       rax,  60
  mov       rdi, 0
  syscall
