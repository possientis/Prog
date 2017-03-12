section .text
global _start

_start:

  mul al  ; al*al -> ax
  mul bl  ; al*bl -> ax
  mul cl  ; al*cl -> ax
  mul dl  ; al*dl -> ax
  mul dil ; al*dil -> ax 
  mul sil ; al*sil -> ax
  mul bpl ; al*bpl -> ax
  mul spl ; al*spl -> ax
  mul r8b ; al*r8b -> ax
  mul r9b ; al*r9b -> ax
  mul r10b ; al*r10b -> ax
  mul r11b ; al*r11b -> ax
  mul r12b ; al*r12b -> ax
  mul r13b ; al*r13b -> ax
  mul r14b ; al*r14b -> ax
  mul r15b ; al*r15b -> ax

  imul al  ; al*al -> ax
  imul bl  ; al*bl -> ax
  imul cl  ; al*cl -> ax
  imul dl  ; al*dl -> ax
  imul dil ; al*dil -> ax 
  imul sil ; al*sil -> ax
  imul bpl ; al*bpl -> ax
  imul spl ; al*spl -> ax
  imul r8b ; al*r8b -> ax
  imul r9b ; al*r9b -> ax
  imul r10b ; al*r10b -> ax
  imul r11b ; al*r11b -> ax
  imul r12b ; al*r12b -> ax
  imul r13b ; al*r13b -> ax
  imul r14b ; al*r14b -> ax
  imul r15b ; al*r15b -> ax

  mul ax  ; ax*ax -> dx:ax
  mul bx  ; ax*bx -> dx:ax
  mul cx  ; ax*cx -> dx:ax
  mul dx  ; ax*dx -> dx:ax
  mul di  ; ax*di -> dx:ax
  mul si  ; ax*si -> dx:ax
  mul bp  ; ax*bp -> dx:ax
  mul sp  ; ax*sp -> dx:ax
  mul r8w  ; ax*r8w -> dx:ax
  mul r9w  ; ax*r9w -> dx:ax
  mul r10w  ; ax*r10w -> dx:ax
  mul r11w  ; ax*r11w -> dx:ax
  mul r12w  ; ax*r12w -> dx:ax
  mul r13w  ; ax*r13w -> dx:ax
  mul r14w  ; ax*r14w -> dx:ax
  mul r15w  ; ax*r15w -> dx:ax

  imul ax  ; ax*ax -> dx:ax
  imul bx  ; ax*bx -> dx:ax
  imul cx  ; ax*cx -> dx:ax
  imul dx  ; ax*dx -> dx:ax
  imul di  ; ax*di -> dx:ax
  imul si  ; ax*si -> dx:ax
  imul bp  ; ax*bp -> dx:ax
  imul sp  ; ax*sp -> dx:ax
  imul r8w  ; ax*r8w -> dx:ax
  imul r9w  ; ax*r9w -> dx:ax
  imul r10w  ; ax*r10w -> dx:ax
  imul r11w  ; ax*r11w -> dx:ax
  imul r12w  ; ax*r12w -> dx:ax
  imul r13w  ; ax*r13w -> dx:ax
  imul r14w  ; ax*r14w -> dx:ax
  imul r15w  ; ax*r15w -> dx:ax

  mul eax   ; eax*eax  -> edx:eax
  mul ebx   ; eax*ebx  -> edx:eax
  mul ecx   ; eax*ecx  -> edx:eax
  mul edx   ; eax*edx  -> edx:eax
  mul edi   ; eax*edi  -> edx:eax
  mul esi   ; eax*esi  -> edx:eax
  mul ebp   ; eax*ebp  -> edx:eax
  mul esp   ; eax*esp  -> edx:eax
  mul r8d   ; eax*r8d  -> edx:eax
  mul r9d   ; eax*r8d  -> edx:eax
  mul r10d   ; eax*r8d  -> edx:eax
  mul r11d   ; eax*r8d  -> edx:eax
  mul r12d   ; eax*r8d  -> edx:eax
  mul r13d   ; eax*r8d  -> edx:eax
  mul r14d   ; eax*r8d  -> edx:eax
  mul r15d   ; eax*r8d  -> edx:eax

  imul eax   ; eax*eax  -> edx:eax
  imul ebx   ; eax*ebx  -> edx:eax
  imul ecx   ; eax*ecx  -> edx:eax
  imul edx   ; eax*edx  -> edx:eax
  imul edi   ; eax*edi  -> edx:eax
  imul esi   ; eax*esi  -> edx:eax
  imul ebp   ; eax*ebp  -> edx:eax
  imul esp   ; eax*esp  -> edx:eax
  imul r8d   ; eax*r8d  -> edx:eax
  imul r9d   ; eax*r8d  -> edx:eax
  imul r10d   ; eax*r8d  -> edx:eax
  imul r11d   ; eax*r8d  -> edx:eax
  imul r12d   ; eax*r8d  -> edx:eax
  imul r13d   ; eax*r8d  -> edx:eax
  imul r14d   ; eax*r8d  -> edx:eax
  imul r15d   ; eax*r8d  -> edx:eax


  mul rax   ; rax*rax  -> rdx:rax
  mul rbx   ; rax*rbx  -> rdx:rax
  mul rcx   ; rax*rcx  -> rdx:rax
  mul rdx   ; rax*rdx  -> rdx:rax
  mul rdi   ; rax*rdi  -> rdx:rax
  mul rsi   ; rax*rsi  -> rdx:rax
  mul rbp   ; rax*rbp  -> rdx:rax
  mul rsp   ; rax*rsp  -> rdx:rax
  mul r8    ; rax*r8   -> rdx:rax
  mul r9    ; rax*r8   -> rdx:rax
  mul r10    ; rax*r8   -> rdx:rax
  mul r11    ; rax*r8   -> rdx:rax
  mul r12    ; rax*r8   -> rdx:rax
  mul r13    ; rax*r8   -> rdx:rax
  mul r14    ; rax*r8   -> rdx:rax
  mul r15    ; rax*r8   -> rdx:rax

  imul rax   ; rax*rax  -> rdx:rax
  imul rbx   ; rax*rbx  -> rdx:rax
  imul rcx   ; rax*rcx  -> rdx:rax
  imul rdx   ; rax*rdx  -> rdx:rax
  imul rdi   ; rax*rdi  -> rdx:rax
  imul rsi   ; rax*rsi  -> rdx:rax
  imul rbp   ; rax*rbp  -> rdx:rax
  imul rsp   ; rax*rsp  -> rdx:rax
  imul r8    ; rax*r8   -> rdx:rax
  imul r9    ; rax*r8   -> rdx:rax
  imul r10    ; rax*r8   -> rdx:rax
  imul r11    ; rax*r8   -> rdx:rax
  imul r12    ; rax*r8   -> rdx:rax
  imul r13    ; rax*r8   -> rdx:rax
  imul r14    ; rax*r8   -> rdx:rax
  imul r15    ; rax*r8   -> rdx:rax


  mov rax, 60
  mov rdi, 0
  syscall
