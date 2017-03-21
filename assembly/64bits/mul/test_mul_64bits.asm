section .bss
output: resb 16 ; 128 bits statically allocated for output

section .text
global test_mul_64bits

; testing assembly multiplication instruction 'mul r'
; the semantics of which is rax*r -> rdx:rax
; 
; input:
; rdi : contains desired value of rax
; rsi : contains desired value of r
; rdx : specifies desired 16 bit register:
;
;     : rdx = 0 -> r = rax (in which case rdi is ignored)
;     : rdx = 1 -> r = rbx
;     : rdx = 2 -> r = rcx
;     : rdx = 3 -> r = rdx
;     : rdx = 4 -> r = rdi
;     : rdx = 5 -> r = rsi
;     : rdx = 6 -> r = rbp
;     : rdx = 7 -> r = rsp
;     : rdx = 8 -> r = r8
;     : rdx = 9 -> r = r9
;     : rdx = 10 -> r = r10
;     : rdx = 11 -> r = r11
;     : rdx = 12 -> r = r12
;     : rdx = 13 -> r = r13
;     : rdx = 14 -> r = r14
;     : rdx = 15 -> r = r15
;
; output: returns pointer to statically allocated 128 bits


test_mul_64bits:
; setting up rax 
  mov rax, rdi      ; rdi -> rax

; if dl == 0, r = rax
_rax:
  cmp dx,0
  jnz _rbx
  mov rax, rsi        ; rsi -> rax (overwrites previous rax value) 
  mul rax             ; rax*rax -> rdx:rax
  jmp exit

; if dl == 1, r = rbx
_rbx:
  dec dx
  jnz _rcx
  mov rbx, rsi    ; rsi -> rbx
  mul rbx         ; rax*rbx -> rdx:rax
  jmp exit

_rcx:

exit:
  mov [output], rax   ; low 64 bits
  mov [output+8], rdx ; high64 bits 
  mov rax, output     ; returning pointer to static 128 bits buffer
  ret


