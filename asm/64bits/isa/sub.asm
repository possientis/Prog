section  .data
  mem8  db 0x00
  mem16 dw 0x0000
  mem32 dd 0x00000000
  mem64 dq 0x0000000000000000

  imm8  equ 0x11
  imm16 equ 0x1122
  imm32 equ 0x11223344
  imm64 equ 0x1122334455667788

section  .text
global _start

_start:

; sub r8,r8

  sub al, al
  sub al, bl
  sub al, cl
  sub al, dl
  sub al, dil
  sub al, sil
  sub al, bpl
  sub al, spl
  sub al, r8b
  sub al, r9b
  sub al, r10b
  sub al, r11b
  sub al, r12b
  sub al, r13b
  sub al, r14b
  sub al, r15b
  sub bl, al
  sub bl, bl
  sub bl, cl
  sub bl, dl
  sub bl, dil
  sub bl, sil
  sub bl, bpl
  sub bl, spl
  sub bl, r8b
  sub bl, r9b
  sub bl, r10b
  sub bl, r11b
  sub bl, r12b
  sub bl, r13b
  sub bl, r14b
  sub bl, r15b
  sub cl, al
  sub cl, bl
  sub cl, cl
  sub cl, dl
  sub cl, dil
  sub cl, sil
  sub cl, bpl
  sub cl, spl
  sub cl, r8b
  sub cl, r9b
  sub cl, r10b
  sub cl, r11b
  sub cl, r12b
  sub cl, r13b
  sub cl, r14b
  sub cl, r15b
  sub dl, al
  sub dl, bl
  sub dl, cl
  sub dl, dl
  sub dl, dil
  sub dl, sil
  sub dl, bpl
  sub dl, spl
  sub dl, r8b
  sub dl, r9b
  sub dl, r10b
  sub dl, r11b
  sub dl, r12b
  sub dl, r13b
  sub dl, r14b
  sub dl, r15b
  sub dil, al
  sub dil, bl
  sub dil, cl
  sub dil, dl
  sub dil, dil
  sub dil, sil
  sub dil, bpl
  sub dil, spl
  sub dil, r8b
  sub dil, r9b
  sub dil, r10b
  sub dil, r11b
  sub dil, r12b
  sub dil, r13b
  sub dil, r14b
  sub dil, r15b
  sub sil, al
  sub sil, bl
  sub sil, cl
  sub sil, dl
  sub sil, dil
  sub sil, sil
  sub sil, bpl
  sub sil, spl
  sub sil, r8b
  sub sil, r9b
  sub sil, r10b
  sub sil, r11b
  sub sil, r12b
  sub sil, r13b
  sub sil, r14b
  sub sil, r15b
  sub bpl, al
  sub bpl, bl
  sub bpl, cl
  sub bpl, dl
  sub bpl, dil
  sub bpl, sil
  sub bpl, bpl
  sub bpl, spl
  sub bpl, r8b
  sub bpl, r9b
  sub bpl, r10b
  sub bpl, r11b
  sub bpl, r12b
  sub bpl, r13b
  sub bpl, r14b
  sub bpl, r15b
  sub spl, al
  sub spl, bl
  sub spl, cl
  sub spl, dl
  sub spl, dil
  sub spl, sil
  sub spl, bpl
  sub spl, spl
  sub spl, r8b
  sub spl, r9b
  sub spl, r10b
  sub spl, r11b
  sub spl, r12b
  sub spl, r13b
  sub spl, r14b
  sub spl, r15b
  sub r8b, al
  sub r8b, bl
  sub r8b, cl
  sub r8b, dl
  sub r8b, dil
  sub r8b, sil
  sub r8b, bpl
  sub r8b, spl
  sub r8b, r8b
  sub r8b, r9b
  sub r8b, r10b
  sub r8b, r11b
  sub r8b, r12b
  sub r8b, r13b
  sub r8b, r14b
  sub r8b, r15b
  sub r9b, al
  sub r9b, bl
  sub r9b, cl
  sub r9b, dl
  sub r9b, dil
  sub r9b, sil
  sub r9b, bpl
  sub r9b, spl
  sub r9b, r8b
  sub r9b, r9b
  sub r9b, r10b
  sub r9b, r11b
  sub r9b, r12b
  sub r9b, r13b
  sub r9b, r14b
  sub r9b, r15b
  sub r10b, al
  sub r10b, bl
  sub r10b, cl
  sub r10b, dl
  sub r10b, dil
  sub r10b, sil
  sub r10b, bpl
  sub r10b, spl
  sub r10b, r8b
  sub r10b, r9b
  sub r10b, r10b
  sub r10b, r11b
  sub r10b, r12b
  sub r10b, r13b
  sub r10b, r14b
  sub r10b, r15b
  sub r11b, al
  sub r11b, bl
  sub r11b, cl
  sub r11b, dl
  sub r11b, dil
  sub r11b, sil
  sub r11b, bpl
  sub r11b, spl
  sub r11b, r8b
  sub r11b, r9b
  sub r11b, r10b
  sub r11b, r11b
  sub r11b, r12b
  sub r11b, r13b
  sub r11b, r14b
  sub r11b, r15b
  sub r12b, al
  sub r12b, bl
  sub r12b, cl
  sub r12b, dl
  sub r12b, dil
  sub r12b, sil
  sub r12b, bpl
  sub r12b, spl
  sub r12b, r8b
  sub r12b, r9b
  sub r12b, r10b
  sub r12b, r11b
  sub r12b, r12b
  sub r12b, r13b
  sub r12b, r14b
  sub r12b, r15b
  sub r13b, al
  sub r13b, bl
  sub r13b, cl
  sub r13b, dl
  sub r13b, dil
  sub r13b, sil
  sub r13b, bpl
  sub r13b, spl
  sub r13b, r8b
  sub r13b, r9b
  sub r13b, r10b
  sub r13b, r11b
  sub r13b, r12b
  sub r13b, r13b
  sub r13b, r14b
  sub r13b, r15b
  sub r14b, al
  sub r14b, bl
  sub r14b, cl
  sub r14b, dl
  sub r14b, dil
  sub r14b, sil
  sub r14b, bpl
  sub r14b, spl
  sub r14b, r8b
  sub r14b, r9b
  sub r14b, r10b
  sub r14b, r11b
  sub r14b, r12b
  sub r14b, r13b
  sub r14b, r14b
  sub r14b, r15b
  sub r15b, al
  sub r15b, bl
  sub r15b, cl
  sub r15b, dl
  sub r15b, dil
  sub r15b, sil
  sub r15b, bpl
  sub r15b, spl
  sub r15b, r8b
  sub r15b, r9b
  sub r15b, r10b
  sub r15b, r11b
  sub r15b, r12b
  sub r15b, r13b
  sub r15b, r14b
  sub r15b, r15b


; sub m8,r8

  sub byte [mem8], al
  sub byte [mem8], bl
  sub byte [mem8], cl
  sub byte [mem8], dl
  sub byte [mem8], dil
  sub byte [mem8], sil
  sub byte [mem8], bpl
  sub byte [mem8], spl
  sub byte [mem8], r8b
  sub byte [mem8], r9b
  sub byte [mem8], r10b
  sub byte [mem8], r11b
  sub byte [mem8], r12b
  sub byte [mem8], r13b
  sub byte [mem8], r14b
  sub byte [mem8], r15b


; sub r8,m8

  sub al, byte [mem8]
  sub bl, byte [mem8]
  sub cl, byte [mem8]
  sub dl, byte [mem8]
  sub dil, byte [mem8]
  sub sil, byte [mem8]
  sub bpl, byte [mem8]
  sub spl, byte [mem8]
  sub r8b, byte [mem8]
  sub r9b, byte [mem8]
  sub r10b, byte [mem8]
  sub r11b, byte [mem8]
  sub r12b, byte [mem8]
  sub r13b, byte [mem8]
  sub r14b, byte [mem8]
  sub r15b, byte [mem8]


; sub r8,i8

  sub al, imm8
  sub bl, imm8
  sub cl, imm8
  sub dl, imm8
  sub dil, imm8
  sub sil, imm8
  sub bpl, imm8
  sub spl, imm8
  sub r8b, imm8
  sub r9b, imm8
  sub r10b, imm8
  sub r11b, imm8
  sub r12b, imm8
  sub r13b, imm8
  sub r14b, imm8
  sub r15b, imm8


; sub m8,i8

  sub byte [mem8], imm8


; sub r16,r16

  sub ax, ax
  sub ax, bx
  sub ax, cx
  sub ax, dx
  sub ax, di
  sub ax, si
  sub ax, bp
  sub ax, sp
  sub ax, r8w
  sub ax, r9w
  sub ax, r10w
  sub ax, r11w
  sub ax, r12w
  sub ax, r13w
  sub ax, r14w
  sub ax, r15w
  sub bx, ax
  sub bx, bx
  sub bx, cx
  sub bx, dx
  sub bx, di
  sub bx, si
  sub bx, bp
  sub bx, sp
  sub bx, r8w
  sub bx, r9w
  sub bx, r10w
  sub bx, r11w
  sub bx, r12w
  sub bx, r13w
  sub bx, r14w
  sub bx, r15w
  sub cx, ax
  sub cx, bx
  sub cx, cx
  sub cx, dx
  sub cx, di
  sub cx, si
  sub cx, bp
  sub cx, sp
  sub cx, r8w
  sub cx, r9w
  sub cx, r10w
  sub cx, r11w
  sub cx, r12w
  sub cx, r13w
  sub cx, r14w
  sub cx, r15w
  sub dx, ax
  sub dx, bx
  sub dx, cx
  sub dx, dx
  sub dx, di
  sub dx, si
  sub dx, bp
  sub dx, sp
  sub dx, r8w
  sub dx, r9w
  sub dx, r10w
  sub dx, r11w
  sub dx, r12w
  sub dx, r13w
  sub dx, r14w
  sub dx, r15w
  sub di, ax
  sub di, bx
  sub di, cx
  sub di, dx
  sub di, di
  sub di, si
  sub di, bp
  sub di, sp
  sub di, r8w
  sub di, r9w
  sub di, r10w
  sub di, r11w
  sub di, r12w
  sub di, r13w
  sub di, r14w
  sub di, r15w
  sub si, ax
  sub si, bx
  sub si, cx
  sub si, dx
  sub si, di
  sub si, si
  sub si, bp
  sub si, sp
  sub si, r8w
  sub si, r9w
  sub si, r10w
  sub si, r11w
  sub si, r12w
  sub si, r13w
  sub si, r14w
  sub si, r15w
  sub bp, ax
  sub bp, bx
  sub bp, cx
  sub bp, dx
  sub bp, di
  sub bp, si
  sub bp, bp
  sub bp, sp
  sub bp, r8w
  sub bp, r9w
  sub bp, r10w
  sub bp, r11w
  sub bp, r12w
  sub bp, r13w
  sub bp, r14w
  sub bp, r15w
  sub sp, ax
  sub sp, bx
  sub sp, cx
  sub sp, dx
  sub sp, di
  sub sp, si
  sub sp, bp
  sub sp, sp
  sub sp, r8w
  sub sp, r9w
  sub sp, r10w
  sub sp, r11w
  sub sp, r12w
  sub sp, r13w
  sub sp, r14w
  sub sp, r15w
  sub r8w, ax
  sub r8w, bx
  sub r8w, cx
  sub r8w, dx
  sub r8w, di
  sub r8w, si
  sub r8w, bp
  sub r8w, sp
  sub r8w, r8w
  sub r8w, r9w
  sub r8w, r10w
  sub r8w, r11w
  sub r8w, r12w
  sub r8w, r13w
  sub r8w, r14w
  sub r8w, r15w
  sub r9w, ax
  sub r9w, bx
  sub r9w, cx
  sub r9w, dx
  sub r9w, di
  sub r9w, si
  sub r9w, bp
  sub r9w, sp
  sub r9w, r8w
  sub r9w, r9w
  sub r9w, r10w
  sub r9w, r11w
  sub r9w, r12w
  sub r9w, r13w
  sub r9w, r14w
  sub r9w, r15w
  sub r10w, ax
  sub r10w, bx
  sub r10w, cx
  sub r10w, dx
  sub r10w, di
  sub r10w, si
  sub r10w, bp
  sub r10w, sp
  sub r10w, r8w
  sub r10w, r9w
  sub r10w, r10w
  sub r10w, r11w
  sub r10w, r12w
  sub r10w, r13w
  sub r10w, r14w
  sub r10w, r15w
  sub r11w, ax
  sub r11w, bx
  sub r11w, cx
  sub r11w, dx
  sub r11w, di
  sub r11w, si
  sub r11w, bp
  sub r11w, sp
  sub r11w, r8w
  sub r11w, r9w
  sub r11w, r10w
  sub r11w, r11w
  sub r11w, r12w
  sub r11w, r13w
  sub r11w, r14w
  sub r11w, r15w
  sub r12w, ax
  sub r12w, bx
  sub r12w, cx
  sub r12w, dx
  sub r12w, di
  sub r12w, si
  sub r12w, bp
  sub r12w, sp
  sub r12w, r8w
  sub r12w, r9w
  sub r12w, r10w
  sub r12w, r11w
  sub r12w, r12w
  sub r12w, r13w
  sub r12w, r14w
  sub r12w, r15w
  sub r13w, ax
  sub r13w, bx
  sub r13w, cx
  sub r13w, dx
  sub r13w, di
  sub r13w, si
  sub r13w, bp
  sub r13w, sp
  sub r13w, r8w
  sub r13w, r9w
  sub r13w, r10w
  sub r13w, r11w
  sub r13w, r12w
  sub r13w, r13w
  sub r13w, r14w
  sub r13w, r15w
  sub r14w, ax
  sub r14w, bx
  sub r14w, cx
  sub r14w, dx
  sub r14w, di
  sub r14w, si
  sub r14w, bp
  sub r14w, sp
  sub r14w, r8w
  sub r14w, r9w
  sub r14w, r10w
  sub r14w, r11w
  sub r14w, r12w
  sub r14w, r13w
  sub r14w, r14w
  sub r14w, r15w
  sub r15w, ax
  sub r15w, bx
  sub r15w, cx
  sub r15w, dx
  sub r15w, di
  sub r15w, si
  sub r15w, bp
  sub r15w, sp
  sub r15w, r8w
  sub r15w, r9w
  sub r15w, r10w
  sub r15w, r11w
  sub r15w, r12w
  sub r15w, r13w
  sub r15w, r14w
  sub r15w, r15w


; sub m16,r16

  sub word [mem16], ax
  sub word [mem16], bx
  sub word [mem16], cx
  sub word [mem16], dx
  sub word [mem16], di
  sub word [mem16], si
  sub word [mem16], bp
  sub word [mem16], sp
  sub word [mem16], r8w
  sub word [mem16], r9w
  sub word [mem16], r10w
  sub word [mem16], r11w
  sub word [mem16], r12w
  sub word [mem16], r13w
  sub word [mem16], r14w
  sub word [mem16], r15w


; sub r16,m16

  sub ax, word [mem16]
  sub bx, word [mem16]
  sub cx, word [mem16]
  sub dx, word [mem16]
  sub di, word [mem16]
  sub si, word [mem16]
  sub bp, word [mem16]
  sub sp, word [mem16]
  sub r8w, word [mem16]
  sub r9w, word [mem16]
  sub r10w, word [mem16]
  sub r11w, word [mem16]
  sub r12w, word [mem16]
  sub r13w, word [mem16]
  sub r14w, word [mem16]
  sub r15w, word [mem16]


; sub r16,i16

  sub ax, imm16
  sub bx, imm16
  sub cx, imm16
  sub dx, imm16
  sub di, imm16
  sub si, imm16
  sub bp, imm16
  sub sp, imm16
  sub r8w, imm16
  sub r9w, imm16
  sub r10w, imm16
  sub r11w, imm16
  sub r12w, imm16
  sub r13w, imm16
  sub r14w, imm16
  sub r15w, imm16


; sub m16,i16

  sub word [mem16], imm16


; sub r32,r32

  sub eax, eax
  sub eax, ebx
  sub eax, ecx
  sub eax, edx
  sub eax, edi
  sub eax, esi
  sub eax, ebp
  sub eax, esp
  sub eax, r8d
  sub eax, r9d
  sub eax, r10d
  sub eax, r11d
  sub eax, r12d
  sub eax, r13d
  sub eax, r14d
  sub eax, r15d
  sub ebx, eax
  sub ebx, ebx
  sub ebx, ecx
  sub ebx, edx
  sub ebx, edi
  sub ebx, esi
  sub ebx, ebp
  sub ebx, esp
  sub ebx, r8d
  sub ebx, r9d
  sub ebx, r10d
  sub ebx, r11d
  sub ebx, r12d
  sub ebx, r13d
  sub ebx, r14d
  sub ebx, r15d
  sub ecx, eax
  sub ecx, ebx
  sub ecx, ecx
  sub ecx, edx
  sub ecx, edi
  sub ecx, esi
  sub ecx, ebp
  sub ecx, esp
  sub ecx, r8d
  sub ecx, r9d
  sub ecx, r10d
  sub ecx, r11d
  sub ecx, r12d
  sub ecx, r13d
  sub ecx, r14d
  sub ecx, r15d
  sub edx, eax
  sub edx, ebx
  sub edx, ecx
  sub edx, edx
  sub edx, edi
  sub edx, esi
  sub edx, ebp
  sub edx, esp
  sub edx, r8d
  sub edx, r9d
  sub edx, r10d
  sub edx, r11d
  sub edx, r12d
  sub edx, r13d
  sub edx, r14d
  sub edx, r15d
  sub edi, eax
  sub edi, ebx
  sub edi, ecx
  sub edi, edx
  sub edi, edi
  sub edi, esi
  sub edi, ebp
  sub edi, esp
  sub edi, r8d
  sub edi, r9d
  sub edi, r10d
  sub edi, r11d
  sub edi, r12d
  sub edi, r13d
  sub edi, r14d
  sub edi, r15d
  sub esi, eax
  sub esi, ebx
  sub esi, ecx
  sub esi, edx
  sub esi, edi
  sub esi, esi
  sub esi, ebp
  sub esi, esp
  sub esi, r8d
  sub esi, r9d
  sub esi, r10d
  sub esi, r11d
  sub esi, r12d
  sub esi, r13d
  sub esi, r14d
  sub esi, r15d
  sub ebp, eax
  sub ebp, ebx
  sub ebp, ecx
  sub ebp, edx
  sub ebp, edi
  sub ebp, esi
  sub ebp, ebp
  sub ebp, esp
  sub ebp, r8d
  sub ebp, r9d
  sub ebp, r10d
  sub ebp, r11d
  sub ebp, r12d
  sub ebp, r13d
  sub ebp, r14d
  sub ebp, r15d
  sub esp, eax
  sub esp, ebx
  sub esp, ecx
  sub esp, edx
  sub esp, edi
  sub esp, esi
  sub esp, ebp
  sub esp, esp
  sub esp, r8d
  sub esp, r9d
  sub esp, r10d
  sub esp, r11d
  sub esp, r12d
  sub esp, r13d
  sub esp, r14d
  sub esp, r15d
  sub r8d, eax
  sub r8d, ebx
  sub r8d, ecx
  sub r8d, edx
  sub r8d, edi
  sub r8d, esi
  sub r8d, ebp
  sub r8d, esp
  sub r8d, r8d
  sub r8d, r9d
  sub r8d, r10d
  sub r8d, r11d
  sub r8d, r12d
  sub r8d, r13d
  sub r8d, r14d
  sub r8d, r15d
  sub r9d, eax
  sub r9d, ebx
  sub r9d, ecx
  sub r9d, edx
  sub r9d, edi
  sub r9d, esi
  sub r9d, ebp
  sub r9d, esp
  sub r9d, r8d
  sub r9d, r9d
  sub r9d, r10d
  sub r9d, r11d
  sub r9d, r12d
  sub r9d, r13d
  sub r9d, r14d
  sub r9d, r15d
  sub r10d, eax
  sub r10d, ebx
  sub r10d, ecx
  sub r10d, edx
  sub r10d, edi
  sub r10d, esi
  sub r10d, ebp
  sub r10d, esp
  sub r10d, r8d
  sub r10d, r9d
  sub r10d, r10d
  sub r10d, r11d
  sub r10d, r12d
  sub r10d, r13d
  sub r10d, r14d
  sub r10d, r15d
  sub r11d, eax
  sub r11d, ebx
  sub r11d, ecx
  sub r11d, edx
  sub r11d, edi
  sub r11d, esi
  sub r11d, ebp
  sub r11d, esp
  sub r11d, r8d
  sub r11d, r9d
  sub r11d, r10d
  sub r11d, r11d
  sub r11d, r12d
  sub r11d, r13d
  sub r11d, r14d
  sub r11d, r15d
  sub r12d, eax
  sub r12d, ebx
  sub r12d, ecx
  sub r12d, edx
  sub r12d, edi
  sub r12d, esi
  sub r12d, ebp
  sub r12d, esp
  sub r12d, r8d
  sub r12d, r9d
  sub r12d, r10d
  sub r12d, r11d
  sub r12d, r12d
  sub r12d, r13d
  sub r12d, r14d
  sub r12d, r15d
  sub r13d, eax
  sub r13d, ebx
  sub r13d, ecx
  sub r13d, edx
  sub r13d, edi
  sub r13d, esi
  sub r13d, ebp
  sub r13d, esp
  sub r13d, r8d
  sub r13d, r9d
  sub r13d, r10d
  sub r13d, r11d
  sub r13d, r12d
  sub r13d, r13d
  sub r13d, r14d
  sub r13d, r15d
  sub r14d, eax
  sub r14d, ebx
  sub r14d, ecx
  sub r14d, edx
  sub r14d, edi
  sub r14d, esi
  sub r14d, ebp
  sub r14d, esp
  sub r14d, r8d
  sub r14d, r9d
  sub r14d, r10d
  sub r14d, r11d
  sub r14d, r12d
  sub r14d, r13d
  sub r14d, r14d
  sub r14d, r15d
  sub r15d, eax
  sub r15d, ebx
  sub r15d, ecx
  sub r15d, edx
  sub r15d, edi
  sub r15d, esi
  sub r15d, ebp
  sub r15d, esp
  sub r15d, r8d
  sub r15d, r9d
  sub r15d, r10d
  sub r15d, r11d
  sub r15d, r12d
  sub r15d, r13d
  sub r15d, r14d
  sub r15d, r15d


; sub m32,r32

  sub dword [mem32], eax
  sub dword [mem32], ebx
  sub dword [mem32], ecx
  sub dword [mem32], edx
  sub dword [mem32], edi
  sub dword [mem32], esi
  sub dword [mem32], ebp
  sub dword [mem32], esp
  sub dword [mem32], r8d
  sub dword [mem32], r9d
  sub dword [mem32], r10d
  sub dword [mem32], r11d
  sub dword [mem32], r12d
  sub dword [mem32], r13d
  sub dword [mem32], r14d
  sub dword [mem32], r15d


; sub r32,m32

  sub eax, dword [mem32]
  sub ebx, dword [mem32]
  sub ecx, dword [mem32]
  sub edx, dword [mem32]
  sub edi, dword [mem32]
  sub esi, dword [mem32]
  sub ebp, dword [mem32]
  sub esp, dword [mem32]
  sub r8d, dword [mem32]
  sub r9d, dword [mem32]
  sub r10d, dword [mem32]
  sub r11d, dword [mem32]
  sub r12d, dword [mem32]
  sub r13d, dword [mem32]
  sub r14d, dword [mem32]
  sub r15d, dword [mem32]


; sub r32,i32

  sub eax, imm32
  sub ebx, imm32
  sub ecx, imm32
  sub edx, imm32
  sub edi, imm32
  sub esi, imm32
  sub ebp, imm32
  sub esp, imm32
  sub r8d, imm32
  sub r9d, imm32
  sub r10d, imm32
  sub r11d, imm32
  sub r12d, imm32
  sub r13d, imm32
  sub r14d, imm32
  sub r15d, imm32


; sub m32,i32

  sub dword [mem32], imm32


; sub r64,r64

  sub rax, rax
  sub rax, rbx
  sub rax, rcx
  sub rax, rdx
  sub rax, rdi
  sub rax, rsi
  sub rax, rbp
  sub rax, rsp
  sub rax, r8
  sub rax, r9
  sub rax, r10
  sub rax, r11
  sub rax, r12
  sub rax, r13
  sub rax, r14
  sub rax, r15
  sub rbx, rax
  sub rbx, rbx
  sub rbx, rcx
  sub rbx, rdx
  sub rbx, rdi
  sub rbx, rsi
  sub rbx, rbp
  sub rbx, rsp
  sub rbx, r8
  sub rbx, r9
  sub rbx, r10
  sub rbx, r11
  sub rbx, r12
  sub rbx, r13
  sub rbx, r14
  sub rbx, r15
  sub rcx, rax
  sub rcx, rbx
  sub rcx, rcx
  sub rcx, rdx
  sub rcx, rdi
  sub rcx, rsi
  sub rcx, rbp
  sub rcx, rsp
  sub rcx, r8
  sub rcx, r9
  sub rcx, r10
  sub rcx, r11
  sub rcx, r12
  sub rcx, r13
  sub rcx, r14
  sub rcx, r15
  sub rdx, rax
  sub rdx, rbx
  sub rdx, rcx
  sub rdx, rdx
  sub rdx, rdi
  sub rdx, rsi
  sub rdx, rbp
  sub rdx, rsp
  sub rdx, r8
  sub rdx, r9
  sub rdx, r10
  sub rdx, r11
  sub rdx, r12
  sub rdx, r13
  sub rdx, r14
  sub rdx, r15
  sub rdi, rax
  sub rdi, rbx
  sub rdi, rcx
  sub rdi, rdx
  sub rdi, rdi
  sub rdi, rsi
  sub rdi, rbp
  sub rdi, rsp
  sub rdi, r8
  sub rdi, r9
  sub rdi, r10
  sub rdi, r11
  sub rdi, r12
  sub rdi, r13
  sub rdi, r14
  sub rdi, r15
  sub rsi, rax
  sub rsi, rbx
  sub rsi, rcx
  sub rsi, rdx
  sub rsi, rdi
  sub rsi, rsi
  sub rsi, rbp
  sub rsi, rsp
  sub rsi, r8
  sub rsi, r9
  sub rsi, r10
  sub rsi, r11
  sub rsi, r12
  sub rsi, r13
  sub rsi, r14
  sub rsi, r15
  sub rbp, rax
  sub rbp, rbx
  sub rbp, rcx
  sub rbp, rdx
  sub rbp, rdi
  sub rbp, rsi
  sub rbp, rbp
  sub rbp, rsp
  sub rbp, r8
  sub rbp, r9
  sub rbp, r10
  sub rbp, r11
  sub rbp, r12
  sub rbp, r13
  sub rbp, r14
  sub rbp, r15
  sub rsp, rax
  sub rsp, rbx
  sub rsp, rcx
  sub rsp, rdx
  sub rsp, rdi
  sub rsp, rsi
  sub rsp, rbp
  sub rsp, rsp
  sub rsp, r8
  sub rsp, r9
  sub rsp, r10
  sub rsp, r11
  sub rsp, r12
  sub rsp, r13
  sub rsp, r14
  sub rsp, r15
  sub r8, rax
  sub r8, rbx
  sub r8, rcx
  sub r8, rdx
  sub r8, rdi
  sub r8, rsi
  sub r8, rbp
  sub r8, rsp
  sub r8, r8
  sub r8, r9
  sub r8, r10
  sub r8, r11
  sub r8, r12
  sub r8, r13
  sub r8, r14
  sub r8, r15
  sub r9, rax
  sub r9, rbx
  sub r9, rcx
  sub r9, rdx
  sub r9, rdi
  sub r9, rsi
  sub r9, rbp
  sub r9, rsp
  sub r9, r8
  sub r9, r9
  sub r9, r10
  sub r9, r11
  sub r9, r12
  sub r9, r13
  sub r9, r14
  sub r9, r15
  sub r10, rax
  sub r10, rbx
  sub r10, rcx
  sub r10, rdx
  sub r10, rdi
  sub r10, rsi
  sub r10, rbp
  sub r10, rsp
  sub r10, r8
  sub r10, r9
  sub r10, r10
  sub r10, r11
  sub r10, r12
  sub r10, r13
  sub r10, r14
  sub r10, r15
  sub r11, rax
  sub r11, rbx
  sub r11, rcx
  sub r11, rdx
  sub r11, rdi
  sub r11, rsi
  sub r11, rbp
  sub r11, rsp
  sub r11, r8
  sub r11, r9
  sub r11, r10
  sub r11, r11
  sub r11, r12
  sub r11, r13
  sub r11, r14
  sub r11, r15
  sub r12, rax
  sub r12, rbx
  sub r12, rcx
  sub r12, rdx
  sub r12, rdi
  sub r12, rsi
  sub r12, rbp
  sub r12, rsp
  sub r12, r8
  sub r12, r9
  sub r12, r10
  sub r12, r11
  sub r12, r12
  sub r12, r13
  sub r12, r14
  sub r12, r15
  sub r13, rax
  sub r13, rbx
  sub r13, rcx
  sub r13, rdx
  sub r13, rdi
  sub r13, rsi
  sub r13, rbp
  sub r13, rsp
  sub r13, r8
  sub r13, r9
  sub r13, r10
  sub r13, r11
  sub r13, r12
  sub r13, r13
  sub r13, r14
  sub r13, r15
  sub r14, rax
  sub r14, rbx
  sub r14, rcx
  sub r14, rdx
  sub r14, rdi
  sub r14, rsi
  sub r14, rbp
  sub r14, rsp
  sub r14, r8
  sub r14, r9
  sub r14, r10
  sub r14, r11
  sub r14, r12
  sub r14, r13
  sub r14, r14
  sub r14, r15
  sub r15, rax
  sub r15, rbx
  sub r15, rcx
  sub r15, rdx
  sub r15, rdi
  sub r15, rsi
  sub r15, rbp
  sub r15, rsp
  sub r15, r8
  sub r15, r9
  sub r15, r10
  sub r15, r11
  sub r15, r12
  sub r15, r13
  sub r15, r14
  sub r15, r15


; sub m64,r64

  sub qword [mem64], rax
  sub qword [mem64], rbx
  sub qword [mem64], rcx
  sub qword [mem64], rdx
  sub qword [mem64], rdi
  sub qword [mem64], rsi
  sub qword [mem64], rbp
  sub qword [mem64], rsp
  sub qword [mem64], r8
  sub qword [mem64], r9
  sub qword [mem64], r10
  sub qword [mem64], r11
  sub qword [mem64], r12
  sub qword [mem64], r13
  sub qword [mem64], r14
  sub qword [mem64], r15


; sub r64,m64

  sub rax, qword [mem64]
  sub rbx, qword [mem64]
  sub rcx, qword [mem64]
  sub rdx, qword [mem64]
  sub rdi, qword [mem64]
  sub rsi, qword [mem64]
  sub rbp, qword [mem64]
  sub rsp, qword [mem64]
  sub r8, qword [mem64]
  sub r9, qword [mem64]
  sub r10, qword [mem64]
  sub r11, qword [mem64]
  sub r12, qword [mem64]
  sub r13, qword [mem64]
  sub r14, qword [mem64]
  sub r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
