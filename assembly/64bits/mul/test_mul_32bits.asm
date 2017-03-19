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
  mov eax, esi    ; rsi -> eax (overwrites previous eax value) 
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

; if dl == 2, r = ecx
_ecx:
  dec dx
  jnz _edx
  mov ecx, esi    ; rsi -> ecx
  mul ecx         ; eax*ecx -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 3, r = edx
_edx:
  dec dx
  jnz _edi
  mov edx, esi    ; rsi -> edx
  mul edx         ; eax*edx -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret


; if dl == 4, r = edi
_edi:
  dec dx
  jnz _esi
  mov edi, esi    ; rsi -> edi
  mul edi         ; eax*edi -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 5, r = esi
_esi:
  dec dx
  jnz _ebp
  mov esi, esi    ; rsi -> esi
  mul esi         ; eax*esi -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 6, r = ebp
; need to save and restore base pointer
_ebp:
  dec dx
  jnz _esp
  mov r8, rbp     ; saving base pointer
  mov ebp, esi    ; rsi -> ebp
  mul ebp         ; eax*ebp -> edx:eax
  mov rbp, r8     ; restoring base pointer
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 7, r = esp
; need to save and restore stack pointer
_esp:
  dec dx
  jnz _r8d
  mov r8, rsp     ; saving stack pointer
  mov esp, esi    ; rsi -> esp
  mul esp         ; eax*esp -> edx:eax
  mov rsp, r8     ; restoring base pointer
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 8, r = r8d
_r8d:
  dec dx
  jnz _r9d
  mov r8d, esi    ; rsi -> r8d
  mul r8d         ; eax*r8d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 9, r = r9d
_r9d:
  dec dx
  jnz _r10d
  mov r9d, esi    ; rsi -> r9d
  mul r9d         ; eax*r9d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 10, r = r10d
_r10d:
  dec dx
  jnz _r11d
  mov r10d, esi   ; rsi -> r10d
  mul r10d        ; eax*r10d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 11, r = r11d
_r11d:
  dec dx
  jnz _r12d
  mov r11d, esi   ; rsi -> r11d
  mul r11d        ; eax*r11d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 12, r = r12d
_r12d:
  dec dx
  jnz _r13d
  mov r12d, esi   ; rsi -> r12d
  mul r12d        ; eax*r12d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 13, r = r13d
_r13d:
  dec dx
  jnz _r14d
  mov r13d, esi   ; rsi -> r13d
  mul r13d        ; eax*r13d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 14, r = r14d
_r14d:
  dec dx
  jnz _r15d
  mov r14d, esi   ; rsi -> r14d
  mul r14d        ; eax*r14d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret

; if dl == 15, r = r15d
_r15d:
  dec dx
  jnz error
  mov r15d, esi   ; rsi -> r15d
  mul r15d        ; eax*r15d -> edx:eax
  shl rdx, 32     ; aligning edx with edx:eax
  add rax, rdx    ; result in rax
  ret



error:
  xor rax,rax
  ret



