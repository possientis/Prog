section .text
global test_mul_16bits

; testing assembly multiplication instruction 'mul r'
; the semantics of which is ax*r -> dx:ax
; 
; input:
; rdi : contains desired value of ax
; rsi : contains desired value of r
; rdx : specifies desired 16 bit register:
;
;     : rdx = 0 -> r = ax (in which case rdi is ignored)
;     : rdx = 1 -> r = bx
;     : rdx = 2 -> r = cx
;     : rdx = 3 -> r = dx
;     : rdx = 4 -> r = di
;     : rdx = 5 -> r = si
;     : rdx = 6 -> r = bp
;     : rdx = 7 -> r = sp
;     : rdx = 8 -> r = r8w
;     : rdx = 9 -> r = r9w
;     : rdx = 10 -> r = r10w
;     : rdx = 11 -> r = r11w
;     : rdx = 12 -> r = r12w
;     : rdx = 13 -> r = r13w
;     : rdx = 14 -> r = r14w
;     : rdx = 15 -> r = r15w
;
; output: returns value of register eax


test_mul_16bits:
; setting up ax 
  mov ax, di      ; rdi -> ax
  and rax, 0xffff ; just in case

; if dl == 0, r = ax
_ax:
  cmp dx,0
  jnz _bx
  mov ax, si      ; rsi -> ax (overwrites previous al value) 
  and rax, 0xffff ; just in case
  mul ax          ; ax*ax -> dx:ax
  and rax, 0xffff ; keeping lower 16 bits
  and rdx, 0xffff ; keeping lower 16 bits
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 1, r = bx
_bx:
  dec dx
  jnz _cx
  mov bx, si      ; rsi -> bx
  and rbx, 0xffff ; just in case
  mul bx          ; ax*bx -> dx:ax
  and rax, 0xffff ; keeping lower 16 bits
  and rdx, 0xffff ; keeping lower 16 bits
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

_cx:


