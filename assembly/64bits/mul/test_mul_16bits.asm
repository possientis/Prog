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

; if dl == 0, r = ax
_ax:
  cmp dx,0
  jnz _bx
  mov ax, si      ; rsi -> ax (overwrites previous al value) 
  mul ax          ; ax*ax -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 1, r = bx
_bx:
  dec dx
  jnz _cx
  mov bx, si      ; rsi -> bx
  mul bx          ; ax*bx -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 2, r = cx
_cx:
  dec dx
  jnz _dx
  mov cx, si      ; rsi -> cx
  mul cx          ; ax*cx -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 3, r = dx
_dx:
  dec dx
  jnz _di
  mov dx, si      ; rsi -> dx
  mul dx          ; ax*dx -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 4, r = di
_di:
  dec dx
  jnz _si
  mov di, si      ; rsi -> di
  mul di          ; ax*di -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 5, r = si
_si:
  dec dx
  jnz _bp
  mov si, si      ; rsi -> si
  mul si          ; ax*si -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 6, r = bp
; need to save and restore base pointer
_bp:
  dec dx
  jnz _sp
  mov r8, rbp     ; saving base pointer
  mov bp, si      ; rsi -> bp
  mul bp          ; ax*bp -> dx:ax
  mov rbp, r8     ; restoring base pointer
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 7, r = sp
; need to save and restore stack pointer
_sp:
  dec dx
  jnz _r8w
  mov r8, rsp     ; saving stack pointer
  mov sp, si      ; rsi -> sp
  mul sp          ; ax*sp -> dx:ax
  mov rsp, r8     ; restoring stack pointer
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 8, r = r8w
_r8w:
  dec dx
  jnz _r9w
  mov r8w, si     ; rsi -> r8w
  mul r8w         ; ax*r8w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 9, r = r9w
_r9w:
  dec dx
  jnz _r10w
  mov r9w, si     ; rsi -> r9w
  mul r9w         ; ax*r9w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 10, r = r10w
_r10w:
  dec dx
  jnz _r11w
  mov r10w, si    ; rsi -> r10w
  mul r10w        ; ax*r10w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 11, r = r11w
_r11w:
  dec dx
  jnz _r12w
  mov r11w, si    ; rsi -> r11w
  mul r11w        ; ax*r11w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret


; if dl == 12, r = r12w
_r12w:
  dec dx
  jnz _r13w
  mov r12w, si    ; rsi -> r12w
  mul r12w        ; ax*r12w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret


; if dl == 13, r = r13w
_r13w:
  dec dx
  jnz _r14w
  mov r13w, si    ; rsi -> r13w
  mul r13w        ; ax*r13w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 14, r = r14w
_r14w:
  dec dx
  jnz _r15w
  mov r14w, si    ; rsi -> r14w
  mul r14w        ; ax*r14w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

; if dl == 15, r = r15w
_r15w:
  dec dx
  jnz error
  mov r15w, si    ; rsi -> r15w
  mul r15w        ; ax*r15w -> dx:ax
  shl rdx, 16     ; aligning dx with dx:ax
  add rax, rdx    ; result in rax
  ret

error:
  xor rax, rax
  ret


