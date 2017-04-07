section .bss
output: resb 16 ; 128 bits statically allocated for output

section .text
global test_mul_64bits

; testing assembly multiplication instruction 'mul <reg>'
; the semantics of which is rax*<reg> -> rdx:rax (unsigned multiplication)
; 
; input:
; rdi : contains desired value of rax
; rsi : contains desired value of <reg>
; rdx : specifies desired 16 bit register:
;
;     : rdx = 0   -> <reg> = rax (in which case rdi is ignored)
;     : rdx = 1   -> <reg> = rbx
;     : rdx = 2   -> <reg> = rcx
;     : rdx = 3   -> <reg> = rdx
;     : rdx = 4   -> <reg> = rdi
;     : rdx = 5   -> <reg> = rsi
;     : rdx = 6   -> <reg> = rbp
;     : rdx = 7   -> <reg> = rsp
;     : rdx = 8   -> <reg> = r8
;     : rdx = 9   -> <reg> = r9
;     : rdx = 10  -> <reg> = r10
;     : rdx = 11  -> <reg> = r11
;     : rdx = 12  -> <reg> = r12
;     : rdx = 13  -> <reg> = r13
;     : rdx = 14  -> <reg> = r14
;     : rdx = 15  -> <reg> = r15
;
; output: returns pointer to statically allocated 128 bits


test_mul_64bits:
; setting up rax 
  mov rax, rdi      ; rdi -> rax

; if dl == 0, <reg> = rax
_rax:
  cmp dx,0
  jnz _rbx
  mov rax, rsi        ; rsi -> rax (overwrites previous rax value) 
  mul rax             ; rax*rax -> rdx:rax
  jmp exit

; if dl == 1, <reg> = rbx
_rbx:
  dec dx
  jnz _rcx
  mov rbx, rsi    ; rsi -> rbx
  mul rbx         ; rax*rbx -> rdx:rax
  jmp exit

; if dl == 2, <reg> = rcx
_rcx:
  dec dx
  jnz _rdx
  mov rcx, rsi    ; rsi -> rcx
  mul rcx         ; rax*rcx -> rdx:rax
  jmp exit

; if dl == 3, <reg> = rdx
_rdx:
  dec dx
  jnz _rdi
  mov rdx, rsi    ; rsi -> rdx
  mul rdx         ; rax*rdx -> rdx:rax
  jmp exit

; if dl == 4, <reg> = rdi
_rdi:
  dec dx
  jnz _rsi
  mov rdi, rsi    ; rsi -> rdi
  mul rdi         ; rax*rdi -> rdx:rax
  jmp exit

; if dl == 5, <reg> = rsi
_rsi:
  dec dx
  jnz _rbp
  mov rsi, rsi    ; rsi -> rsi
  mul rsi         ; rax*rsi -> rdx:rax
  jmp exit

; if dl == 6, <reg> = rbp
_rbp:
  dec dx
  jnz _rsp
  mov r8,  rbp    ; saving rbp
  mov rbp, rsi    ; rsi -> rbp
  mul rbp         ; rax*rbp -> rdx:rax
  mov rbp, r8     ; restoring rbp 
  jmp exit

; if dl == 7, <reg> = rsp
_rsp:
  dec dx
  jnz _r8
  mov r8,  rsp    ; saving rsp
  mov rsp, rsi    ; rsi -> rsp
  mul rsp         ; rax*rsp -> rdx:rax
  mov rsp, r8     ; restoring rsp 
  jmp exit

; if dl == 8, <reg> = r8
_r8:
  dec dx
  jnz _r9
  mov r8, rsi     ; rsi -> r8
  mul r8          ; rax*r8 -> rdx:rax
  jmp exit

; if dl == 9, <reg> = r9
_r9:
  dec dx
  jnz _r10
  mov r9, rsi     ; rsi -> r9
  mul r9          ; rax*r9 -> rdx:rax
  jmp exit

; if dl == 10, <reg> = r10
_r10:
  dec dx
  jnz _r11
  mov r10, rsi     ; rsi -> r10
  mul r10          ; rax*r10 -> rdx:rax
  jmp exit

; if dl == 11, <reg> = r11
_r11:
  dec dx
  jnz _r12
  mov r11, rsi     ; rsi -> r11
  mul r11          ; rax*r11 -> rdx:rax
  jmp exit

; if dl == 12, <reg> = r12
_r12:
  dec dx
  jnz _r13
  mov r12, rsi     ; rsi -> r12
  mul r12          ; rax*r12 -> rdx:rax
  jmp exit

; if dl == 13, <reg> = r13
_r13:
  dec dx
  jnz _r14
  mov r13, rsi     ; rsi -> r13
  mul r13          ; rax*r13 -> rdx:rax
  jmp exit

; if dl == 14, <reg> = r14
_r14:
  dec dx
  jnz _r15
  mov r14, rsi     ; rsi -> r14
  mul r14          ; rax*r14 -> rdx:rax
  jmp exit

; if dl == 15, <reg> = r15
_r15:
  dec dx
  jnz error
  mov r15, rsi     ; rsi -> r15
  mul r15          ; rax*r15 -> rdx:rax

exit:
  mov [output], rax   ; low 64 bits
  mov [output+8], rdx ; high64 bits 
  mov rax, output     ; returning pointer to static 128 bits buffer
  ret

error:
  xor rax, rax
  ret

