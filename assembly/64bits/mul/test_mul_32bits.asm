section .text
global test_mul_32bits

; testing assembly multiplication instruction 'mul r'
; the semantics of which is eax*r -> edx:eax
; 
; input:
; rdi : contains desired value of eax
; rsi : contains desired value of r
; rdx : specifies desired 16 bit register:
;
;     : rdx = 0 -> r = eax (in which case rdi is ignored)
;     : rdx = 1 -> r = ebx
;     : rdx = 2 -> r = ecx
;     : rdx = 3 -> r = edx
;     : rdx = 4 -> r = edi
;     : rdx = 5 -> r = esi
;     : rdx = 6 -> r = ebp
;     : rdx = 7 -> r = esp
;     : rdx = 8 -> r = r8d
;     : rdx = 9 -> r = r9d
;     : rdx = 10 -> r = r10d
;     : rdx = 11 -> r = r11d
;     : rdx = 12 -> r = r12d
;     : rdx = 13 -> r = r13d
;     : rdx = 14 -> r = r14d
;     : rdx = 15 -> r = r15d
;
; output: returns value of register rax


test_mul_32bits:
; setting up eax 
  mov eax, edi      ; rdi -> eax

; if dl == 0, r = ax
_eax:
  cmp dx,0
  jnz _ebx
  mov eax, esi    ; rsi -> eax (overwrites previous al value) 
  mul eax         ; eax*eax -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 1, r = ebx
_ebx:
  dec dx
  jnz _ecx
  mov ebx, esi    ; rsi -> ebx
  mul ebx         ; eax*ebx -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

_ecx:



