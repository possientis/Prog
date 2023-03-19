        section .text
        global quadASMFunction
        extern quadFunction

; This assembly function calls a C (or C++ depending on linking) function.
quadASMFunction:    ; (index, x1, x2, x3, x4, x5, x6, x7, x8)
                    ; index : rdi
                    ; x1    : rsi
                    ; x2    : rdx
                    ; x3    ; rcx
                    ; x4    ; r8
                    ; x5    ; r9
                    ; x6    ; stack pushed last
                    ; x7    ; stack pushed second
                    ; x8    ; stack pushed first
  ; prologue 
  push rbp
  mov  rbp, rsp
  sub  rsp, 64      ; allocating stack space for 8 quad

  ; saving arguments
  mov rax, rdi      ; index
  mov [rbp-8],  rsi ; x1
  mov [rbp-16], rdx ; x2
  mov [rbp-24], rcx ; x3
  mov [rbp-32], r8  ; x4
  mov [rbp-40], r9  ; x5

  mov r10, [rbp+16] 
  mov [rbp-48], r10 ; x6
  
  mov r10, [rbp+24] 
  mov [rbp-56], r10 ; x7

  mov r10, [rbp+32]
  mov [rbp-64], r10 ; x8

  ; returning relevant argument

  ; instead of simply picking the argument and returning it,
  ;  we shall call C/C++ function instead:

  mov   rdi, rax
  mov   rsi, [rbp-8]
  mov   rdx, [rbp-16]
  mov   rcx, [rbp-24]
  mov   r8,  [rbp-32]
  mov   r9,  [rbp-40]

  mov   rax, [rbp-64]
  push  rax

  mov   rax, [rbp-56]
  push rax

  mov   rax, [rbp-48]
  push rax

  call quadFunction ; result in rax
  add   rsp, 24     ; stack clean up

  ; epilogue
  leave
  ret  


