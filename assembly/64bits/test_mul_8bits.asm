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
  mov dil, sil    ; rsi -> dl
  and rdi, 0xff   ; just in case
  mul dil         ; al*dl -> ax
  and rax, 0xffff ; return ax
  ret
  
_sil:

  
