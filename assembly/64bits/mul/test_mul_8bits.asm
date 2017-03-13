section .text
global test_mul_8bits

; testing assembly multiplication instruction 'mul r'
; the semantics of which is al*r -> ax
; 
; input:
; rdi : contains desired value of al
; rsi : contains desired value of r
; rdx : specifies desired 8 bit register:
;
;     : rdx = 0 -> r = al (in which case rdi is ignored)
;     : rdx = 1 -> r = bl
;     : rdx = 2 -> r = cl
;     : rdx = 3 -> r = dl
;     : rdx = 4 -> r = dil
;     : rdx = 5 -> r = sil
;     : rdx = 6 -> r = bpl
;     : rdx = 7 -> r = spl
;     : rdx = 8 -> r = r8b
;     : rdx = 9 -> r = r9b
;     : rdx = 10 -> r = r10b
;     : rdx = 11 -> r = r11b
;     : rdx = 12 -> r = r12b
;     : rdx = 13 -> r = r13b
;     : rdx = 14 -> r = r14b
;     : rdx = 15 -> r = r15b
;
; output: returns value of register ax


test_mul_8bits:
; setting up al 
  mov al,dil      ; rdi -> al
  and rax, 0xff   ; just in case

; if dl == 0, r = al
_al:
  cmp dl,0
  jnz _bl
  mov al, sil     ; rsi -> al (overwrites previous al value) 
  and rax, 0xff   ; just in case
  mul al          ; al*al -> ax
  and rax, 0xffff ; returing ax
  ret

; if dl == 1, r = bl
_bl:
  dec dl
  jnz _cl
  mov bl, sil     ; rsi -> bl
  and rbx, 0xff   ; just in case
  mul bl          ; al*bl -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 2, r = cl
_cl:
  dec dl
  jnz _dl
  mov cl, sil     ; rsi -> cl
  and rcx, 0xff   ; just in case
  mul cl          ; al*cl -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 3, r = dl
_dl:
  dec dl
  jnz _dil
  mov dl, sil     ; rsi -> dl
  and rdx, 0xff   ; just in case
  mul dl          ; al*dl -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 4, r = dil
_dil:
  dec dl
  jnz _sil
  mov dil, sil    ; rsi -> dil
  and rdi, 0xff   ; just in case
  mul dil         ; al*dil -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 5, r = sil
_sil:
  dec dl
  jnz _bpl
  mov sil, sil    ; rsi -> sil
  and rsi, 0xff   ; just in case
  mul sil         ; al*sil -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 6, r = bpl
; need to save base pointer and restore it
_bpl:
  dec dl
  jnz _spl
  mov r8, rbp     ; saving base pointer 
  mov bpl, sil    ; rsi -> bpl
  and rbp, 0xff   ; just in case
  mul bpl         ; al*bpl -> ax
  mov rbp, r8     ; restoring base pointer
  and rax, 0xffff ; return ax
  ret

; if dl == 7, r = spl
; need to save stack pointer and restore it
_spl:
  dec dl
  jnz _r8b
  mov r8, rsp     ; saving stack pointer
  mov spl, sil    ; rsi -> spl
  and rsp, 0xff   ; just in case
  mul spl         ; al*spl -> ax
  mov rsp,r8      ; restoring stack pointer
  and rax, 0xffff ; return ax
  ret

; if dl == 8, r = r8b
_r8b:
  dec dl
  jnz _r9b
  mov r8b, sil    ; rsi -> r8b
  and r8, 0xff    ; just in case
  mul r8b         ; al*r8b -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 9, r = r9b
_r9b:
  dec dl
  jnz _r10b
  mov r9b, sil    ; rsi -> r9b
  and r9, 0xff    ; just in case
  mul r9b         ; al*r9b -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 10, r = r10b
_r10b:
  dec dl
  jnz _r11b
  mov r10b, sil    ; rsi -> r10b
  and r10, 0xff    ; just in case
  mul r10b         ; al*r10b -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 11, r = r11b
_r11b:
  dec dl
  jnz _r12b
  mov r11b, sil    ; rsi -> r11b
  and r11, 0xff    ; just in case
  mul r11b         ; al*r11b -> ax
  and rax, 0xffff ; return ax
  ret
 
; if dl == 12, r = r12b
_r12b:
  dec dl
  jnz _r13b
  mov r12b, sil    ; rsi -> r12b
  and r12, 0xff    ; just in case
  mul r12b         ; al*r12b -> ax
  and rax, 0xffff ; return ax
  ret
 
; if dl == 13, r = r13b
_r13b:
  dec dl
  jnz _r14b
  mov r13b, sil    ; rsi -> r13b
  and r13, 0xff    ; just in case
  mul r13b         ; al*r13b -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 14, r = r14b
_r14b:
  dec dl
  jnz _r15b
  mov r14b, sil    ; rsi -> r14b
  and r14, 0xff    ; just in case
  mul r14b         ; al*r14b -> ax
  and rax, 0xffff ; return ax
  ret

; if dl == 15, r = r15b
_r15b:
  dec dl
  jnz error
  mov r15b, sil    ; rsi -> r15b
  and r15, 0xff    ; just in case
  mul r15b         ; al*r15b -> ax
  and rax, 0xffff ; return ax
  ret
 
error:
  mov rax,0
  ret

