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

; sbb r8,r8

  sbb al, al
  sbb al, bl
  sbb al, cl
  sbb al, dl
  sbb al, dil
  sbb al, sil
  sbb al, bpl
  sbb al, spl
  sbb al, r8b
  sbb al, r9b
  sbb al, r10b
  sbb al, r11b
  sbb al, r12b
  sbb al, r13b
  sbb al, r14b
  sbb al, r15b
  sbb bl, al
  sbb bl, bl
  sbb bl, cl
  sbb bl, dl
  sbb bl, dil
  sbb bl, sil
  sbb bl, bpl
  sbb bl, spl
  sbb bl, r8b
  sbb bl, r9b
  sbb bl, r10b
  sbb bl, r11b
  sbb bl, r12b
  sbb bl, r13b
  sbb bl, r14b
  sbb bl, r15b
  sbb cl, al
  sbb cl, bl
  sbb cl, cl
  sbb cl, dl
  sbb cl, dil
  sbb cl, sil
  sbb cl, bpl
  sbb cl, spl
  sbb cl, r8b
  sbb cl, r9b
  sbb cl, r10b
  sbb cl, r11b
  sbb cl, r12b
  sbb cl, r13b
  sbb cl, r14b
  sbb cl, r15b
  sbb dl, al
  sbb dl, bl
  sbb dl, cl
  sbb dl, dl
  sbb dl, dil
  sbb dl, sil
  sbb dl, bpl
  sbb dl, spl
  sbb dl, r8b
  sbb dl, r9b
  sbb dl, r10b
  sbb dl, r11b
  sbb dl, r12b
  sbb dl, r13b
  sbb dl, r14b
  sbb dl, r15b
  sbb dil, al
  sbb dil, bl
  sbb dil, cl
  sbb dil, dl
  sbb dil, dil
  sbb dil, sil
  sbb dil, bpl
  sbb dil, spl
  sbb dil, r8b
  sbb dil, r9b
  sbb dil, r10b
  sbb dil, r11b
  sbb dil, r12b
  sbb dil, r13b
  sbb dil, r14b
  sbb dil, r15b
  sbb sil, al
  sbb sil, bl
  sbb sil, cl
  sbb sil, dl
  sbb sil, dil
  sbb sil, sil
  sbb sil, bpl
  sbb sil, spl
  sbb sil, r8b
  sbb sil, r9b
  sbb sil, r10b
  sbb sil, r11b
  sbb sil, r12b
  sbb sil, r13b
  sbb sil, r14b
  sbb sil, r15b
  sbb bpl, al
  sbb bpl, bl
  sbb bpl, cl
  sbb bpl, dl
  sbb bpl, dil
  sbb bpl, sil
  sbb bpl, bpl
  sbb bpl, spl
  sbb bpl, r8b
  sbb bpl, r9b
  sbb bpl, r10b
  sbb bpl, r11b
  sbb bpl, r12b
  sbb bpl, r13b
  sbb bpl, r14b
  sbb bpl, r15b
  sbb spl, al
  sbb spl, bl
  sbb spl, cl
  sbb spl, dl
  sbb spl, dil
  sbb spl, sil
  sbb spl, bpl
  sbb spl, spl
  sbb spl, r8b
  sbb spl, r9b
  sbb spl, r10b
  sbb spl, r11b
  sbb spl, r12b
  sbb spl, r13b
  sbb spl, r14b
  sbb spl, r15b
  sbb r8b, al
  sbb r8b, bl
  sbb r8b, cl
  sbb r8b, dl
  sbb r8b, dil
  sbb r8b, sil
  sbb r8b, bpl
  sbb r8b, spl
  sbb r8b, r8b
  sbb r8b, r9b
  sbb r8b, r10b
  sbb r8b, r11b
  sbb r8b, r12b
  sbb r8b, r13b
  sbb r8b, r14b
  sbb r8b, r15b
  sbb r9b, al
  sbb r9b, bl
  sbb r9b, cl
  sbb r9b, dl
  sbb r9b, dil
  sbb r9b, sil
  sbb r9b, bpl
  sbb r9b, spl
  sbb r9b, r8b
  sbb r9b, r9b
  sbb r9b, r10b
  sbb r9b, r11b
  sbb r9b, r12b
  sbb r9b, r13b
  sbb r9b, r14b
  sbb r9b, r15b
  sbb r10b, al
  sbb r10b, bl
  sbb r10b, cl
  sbb r10b, dl
  sbb r10b, dil
  sbb r10b, sil
  sbb r10b, bpl
  sbb r10b, spl
  sbb r10b, r8b
  sbb r10b, r9b
  sbb r10b, r10b
  sbb r10b, r11b
  sbb r10b, r12b
  sbb r10b, r13b
  sbb r10b, r14b
  sbb r10b, r15b
  sbb r11b, al
  sbb r11b, bl
  sbb r11b, cl
  sbb r11b, dl
  sbb r11b, dil
  sbb r11b, sil
  sbb r11b, bpl
  sbb r11b, spl
  sbb r11b, r8b
  sbb r11b, r9b
  sbb r11b, r10b
  sbb r11b, r11b
  sbb r11b, r12b
  sbb r11b, r13b
  sbb r11b, r14b
  sbb r11b, r15b
  sbb r12b, al
  sbb r12b, bl
  sbb r12b, cl
  sbb r12b, dl
  sbb r12b, dil
  sbb r12b, sil
  sbb r12b, bpl
  sbb r12b, spl
  sbb r12b, r8b
  sbb r12b, r9b
  sbb r12b, r10b
  sbb r12b, r11b
  sbb r12b, r12b
  sbb r12b, r13b
  sbb r12b, r14b
  sbb r12b, r15b
  sbb r13b, al
  sbb r13b, bl
  sbb r13b, cl
  sbb r13b, dl
  sbb r13b, dil
  sbb r13b, sil
  sbb r13b, bpl
  sbb r13b, spl
  sbb r13b, r8b
  sbb r13b, r9b
  sbb r13b, r10b
  sbb r13b, r11b
  sbb r13b, r12b
  sbb r13b, r13b
  sbb r13b, r14b
  sbb r13b, r15b
  sbb r14b, al
  sbb r14b, bl
  sbb r14b, cl
  sbb r14b, dl
  sbb r14b, dil
  sbb r14b, sil
  sbb r14b, bpl
  sbb r14b, spl
  sbb r14b, r8b
  sbb r14b, r9b
  sbb r14b, r10b
  sbb r14b, r11b
  sbb r14b, r12b
  sbb r14b, r13b
  sbb r14b, r14b
  sbb r14b, r15b
  sbb r15b, al
  sbb r15b, bl
  sbb r15b, cl
  sbb r15b, dl
  sbb r15b, dil
  sbb r15b, sil
  sbb r15b, bpl
  sbb r15b, spl
  sbb r15b, r8b
  sbb r15b, r9b
  sbb r15b, r10b
  sbb r15b, r11b
  sbb r15b, r12b
  sbb r15b, r13b
  sbb r15b, r14b
  sbb r15b, r15b


; sbb m8,r8

  sbb byte [mem8], al
  sbb byte [mem8], bl
  sbb byte [mem8], cl
  sbb byte [mem8], dl
  sbb byte [mem8], dil
  sbb byte [mem8], sil
  sbb byte [mem8], bpl
  sbb byte [mem8], spl
  sbb byte [mem8], r8b
  sbb byte [mem8], r9b
  sbb byte [mem8], r10b
  sbb byte [mem8], r11b
  sbb byte [mem8], r12b
  sbb byte [mem8], r13b
  sbb byte [mem8], r14b
  sbb byte [mem8], r15b


; sbb r8,m8

  sbb al, byte [mem8]
  sbb bl, byte [mem8]
  sbb cl, byte [mem8]
  sbb dl, byte [mem8]
  sbb dil, byte [mem8]
  sbb sil, byte [mem8]
  sbb bpl, byte [mem8]
  sbb spl, byte [mem8]
  sbb r8b, byte [mem8]
  sbb r9b, byte [mem8]
  sbb r10b, byte [mem8]
  sbb r11b, byte [mem8]
  sbb r12b, byte [mem8]
  sbb r13b, byte [mem8]
  sbb r14b, byte [mem8]
  sbb r15b, byte [mem8]


; sbb r8,i8

  sbb al, imm8
  sbb bl, imm8
  sbb cl, imm8
  sbb dl, imm8
  sbb dil, imm8
  sbb sil, imm8
  sbb bpl, imm8
  sbb spl, imm8
  sbb r8b, imm8
  sbb r9b, imm8
  sbb r10b, imm8
  sbb r11b, imm8
  sbb r12b, imm8
  sbb r13b, imm8
  sbb r14b, imm8
  sbb r15b, imm8


; sbb m8,i8

  sbb byte [mem8], imm8


; sbb r16,r16

  sbb ax, ax
  sbb ax, bx
  sbb ax, cx
  sbb ax, dx
  sbb ax, di
  sbb ax, si
  sbb ax, bp
  sbb ax, sp
  sbb ax, r8w
  sbb ax, r9w
  sbb ax, r10w
  sbb ax, r11w
  sbb ax, r12w
  sbb ax, r13w
  sbb ax, r14w
  sbb ax, r15w
  sbb bx, ax
  sbb bx, bx
  sbb bx, cx
  sbb bx, dx
  sbb bx, di
  sbb bx, si
  sbb bx, bp
  sbb bx, sp
  sbb bx, r8w
  sbb bx, r9w
  sbb bx, r10w
  sbb bx, r11w
  sbb bx, r12w
  sbb bx, r13w
  sbb bx, r14w
  sbb bx, r15w
  sbb cx, ax
  sbb cx, bx
  sbb cx, cx
  sbb cx, dx
  sbb cx, di
  sbb cx, si
  sbb cx, bp
  sbb cx, sp
  sbb cx, r8w
  sbb cx, r9w
  sbb cx, r10w
  sbb cx, r11w
  sbb cx, r12w
  sbb cx, r13w
  sbb cx, r14w
  sbb cx, r15w
  sbb dx, ax
  sbb dx, bx
  sbb dx, cx
  sbb dx, dx
  sbb dx, di
  sbb dx, si
  sbb dx, bp
  sbb dx, sp
  sbb dx, r8w
  sbb dx, r9w
  sbb dx, r10w
  sbb dx, r11w
  sbb dx, r12w
  sbb dx, r13w
  sbb dx, r14w
  sbb dx, r15w
  sbb di, ax
  sbb di, bx
  sbb di, cx
  sbb di, dx
  sbb di, di
  sbb di, si
  sbb di, bp
  sbb di, sp
  sbb di, r8w
  sbb di, r9w
  sbb di, r10w
  sbb di, r11w
  sbb di, r12w
  sbb di, r13w
  sbb di, r14w
  sbb di, r15w
  sbb si, ax
  sbb si, bx
  sbb si, cx
  sbb si, dx
  sbb si, di
  sbb si, si
  sbb si, bp
  sbb si, sp
  sbb si, r8w
  sbb si, r9w
  sbb si, r10w
  sbb si, r11w
  sbb si, r12w
  sbb si, r13w
  sbb si, r14w
  sbb si, r15w
  sbb bp, ax
  sbb bp, bx
  sbb bp, cx
  sbb bp, dx
  sbb bp, di
  sbb bp, si
  sbb bp, bp
  sbb bp, sp
  sbb bp, r8w
  sbb bp, r9w
  sbb bp, r10w
  sbb bp, r11w
  sbb bp, r12w
  sbb bp, r13w
  sbb bp, r14w
  sbb bp, r15w
  sbb sp, ax
  sbb sp, bx
  sbb sp, cx
  sbb sp, dx
  sbb sp, di
  sbb sp, si
  sbb sp, bp
  sbb sp, sp
  sbb sp, r8w
  sbb sp, r9w
  sbb sp, r10w
  sbb sp, r11w
  sbb sp, r12w
  sbb sp, r13w
  sbb sp, r14w
  sbb sp, r15w
  sbb r8w, ax
  sbb r8w, bx
  sbb r8w, cx
  sbb r8w, dx
  sbb r8w, di
  sbb r8w, si
  sbb r8w, bp
  sbb r8w, sp
  sbb r8w, r8w
  sbb r8w, r9w
  sbb r8w, r10w
  sbb r8w, r11w
  sbb r8w, r12w
  sbb r8w, r13w
  sbb r8w, r14w
  sbb r8w, r15w
  sbb r9w, ax
  sbb r9w, bx
  sbb r9w, cx
  sbb r9w, dx
  sbb r9w, di
  sbb r9w, si
  sbb r9w, bp
  sbb r9w, sp
  sbb r9w, r8w
  sbb r9w, r9w
  sbb r9w, r10w
  sbb r9w, r11w
  sbb r9w, r12w
  sbb r9w, r13w
  sbb r9w, r14w
  sbb r9w, r15w
  sbb r10w, ax
  sbb r10w, bx
  sbb r10w, cx
  sbb r10w, dx
  sbb r10w, di
  sbb r10w, si
  sbb r10w, bp
  sbb r10w, sp
  sbb r10w, r8w
  sbb r10w, r9w
  sbb r10w, r10w
  sbb r10w, r11w
  sbb r10w, r12w
  sbb r10w, r13w
  sbb r10w, r14w
  sbb r10w, r15w
  sbb r11w, ax
  sbb r11w, bx
  sbb r11w, cx
  sbb r11w, dx
  sbb r11w, di
  sbb r11w, si
  sbb r11w, bp
  sbb r11w, sp
  sbb r11w, r8w
  sbb r11w, r9w
  sbb r11w, r10w
  sbb r11w, r11w
  sbb r11w, r12w
  sbb r11w, r13w
  sbb r11w, r14w
  sbb r11w, r15w
  sbb r12w, ax
  sbb r12w, bx
  sbb r12w, cx
  sbb r12w, dx
  sbb r12w, di
  sbb r12w, si
  sbb r12w, bp
  sbb r12w, sp
  sbb r12w, r8w
  sbb r12w, r9w
  sbb r12w, r10w
  sbb r12w, r11w
  sbb r12w, r12w
  sbb r12w, r13w
  sbb r12w, r14w
  sbb r12w, r15w
  sbb r13w, ax
  sbb r13w, bx
  sbb r13w, cx
  sbb r13w, dx
  sbb r13w, di
  sbb r13w, si
  sbb r13w, bp
  sbb r13w, sp
  sbb r13w, r8w
  sbb r13w, r9w
  sbb r13w, r10w
  sbb r13w, r11w
  sbb r13w, r12w
  sbb r13w, r13w
  sbb r13w, r14w
  sbb r13w, r15w
  sbb r14w, ax
  sbb r14w, bx
  sbb r14w, cx
  sbb r14w, dx
  sbb r14w, di
  sbb r14w, si
  sbb r14w, bp
  sbb r14w, sp
  sbb r14w, r8w
  sbb r14w, r9w
  sbb r14w, r10w
  sbb r14w, r11w
  sbb r14w, r12w
  sbb r14w, r13w
  sbb r14w, r14w
  sbb r14w, r15w
  sbb r15w, ax
  sbb r15w, bx
  sbb r15w, cx
  sbb r15w, dx
  sbb r15w, di
  sbb r15w, si
  sbb r15w, bp
  sbb r15w, sp
  sbb r15w, r8w
  sbb r15w, r9w
  sbb r15w, r10w
  sbb r15w, r11w
  sbb r15w, r12w
  sbb r15w, r13w
  sbb r15w, r14w
  sbb r15w, r15w


; sbb m16,r16

  sbb word [mem16], ax
  sbb word [mem16], bx
  sbb word [mem16], cx
  sbb word [mem16], dx
  sbb word [mem16], di
  sbb word [mem16], si
  sbb word [mem16], bp
  sbb word [mem16], sp
  sbb word [mem16], r8w
  sbb word [mem16], r9w
  sbb word [mem16], r10w
  sbb word [mem16], r11w
  sbb word [mem16], r12w
  sbb word [mem16], r13w
  sbb word [mem16], r14w
  sbb word [mem16], r15w


; sbb r16,m16

  sbb ax, word [mem16]
  sbb bx, word [mem16]
  sbb cx, word [mem16]
  sbb dx, word [mem16]
  sbb di, word [mem16]
  sbb si, word [mem16]
  sbb bp, word [mem16]
  sbb sp, word [mem16]
  sbb r8w, word [mem16]
  sbb r9w, word [mem16]
  sbb r10w, word [mem16]
  sbb r11w, word [mem16]
  sbb r12w, word [mem16]
  sbb r13w, word [mem16]
  sbb r14w, word [mem16]
  sbb r15w, word [mem16]


; sbb r16,i16

  sbb ax, imm16
  sbb bx, imm16
  sbb cx, imm16
  sbb dx, imm16
  sbb di, imm16
  sbb si, imm16
  sbb bp, imm16
  sbb sp, imm16
  sbb r8w, imm16
  sbb r9w, imm16
  sbb r10w, imm16
  sbb r11w, imm16
  sbb r12w, imm16
  sbb r13w, imm16
  sbb r14w, imm16
  sbb r15w, imm16


; sbb m16,i16

  sbb word [mem16], imm16


; sbb r32,r32

  sbb eax, eax
  sbb eax, ebx
  sbb eax, ecx
  sbb eax, edx
  sbb eax, edi
  sbb eax, esi
  sbb eax, ebp
  sbb eax, esp
  sbb eax, r8d
  sbb eax, r9d
  sbb eax, r10d
  sbb eax, r11d
  sbb eax, r12d
  sbb eax, r13d
  sbb eax, r14d
  sbb eax, r15d
  sbb ebx, eax
  sbb ebx, ebx
  sbb ebx, ecx
  sbb ebx, edx
  sbb ebx, edi
  sbb ebx, esi
  sbb ebx, ebp
  sbb ebx, esp
  sbb ebx, r8d
  sbb ebx, r9d
  sbb ebx, r10d
  sbb ebx, r11d
  sbb ebx, r12d
  sbb ebx, r13d
  sbb ebx, r14d
  sbb ebx, r15d
  sbb ecx, eax
  sbb ecx, ebx
  sbb ecx, ecx
  sbb ecx, edx
  sbb ecx, edi
  sbb ecx, esi
  sbb ecx, ebp
  sbb ecx, esp
  sbb ecx, r8d
  sbb ecx, r9d
  sbb ecx, r10d
  sbb ecx, r11d
  sbb ecx, r12d
  sbb ecx, r13d
  sbb ecx, r14d
  sbb ecx, r15d
  sbb edx, eax
  sbb edx, ebx
  sbb edx, ecx
  sbb edx, edx
  sbb edx, edi
  sbb edx, esi
  sbb edx, ebp
  sbb edx, esp
  sbb edx, r8d
  sbb edx, r9d
  sbb edx, r10d
  sbb edx, r11d
  sbb edx, r12d
  sbb edx, r13d
  sbb edx, r14d
  sbb edx, r15d
  sbb edi, eax
  sbb edi, ebx
  sbb edi, ecx
  sbb edi, edx
  sbb edi, edi
  sbb edi, esi
  sbb edi, ebp
  sbb edi, esp
  sbb edi, r8d
  sbb edi, r9d
  sbb edi, r10d
  sbb edi, r11d
  sbb edi, r12d
  sbb edi, r13d
  sbb edi, r14d
  sbb edi, r15d
  sbb esi, eax
  sbb esi, ebx
  sbb esi, ecx
  sbb esi, edx
  sbb esi, edi
  sbb esi, esi
  sbb esi, ebp
  sbb esi, esp
  sbb esi, r8d
  sbb esi, r9d
  sbb esi, r10d
  sbb esi, r11d
  sbb esi, r12d
  sbb esi, r13d
  sbb esi, r14d
  sbb esi, r15d
  sbb ebp, eax
  sbb ebp, ebx
  sbb ebp, ecx
  sbb ebp, edx
  sbb ebp, edi
  sbb ebp, esi
  sbb ebp, ebp
  sbb ebp, esp
  sbb ebp, r8d
  sbb ebp, r9d
  sbb ebp, r10d
  sbb ebp, r11d
  sbb ebp, r12d
  sbb ebp, r13d
  sbb ebp, r14d
  sbb ebp, r15d
  sbb esp, eax
  sbb esp, ebx
  sbb esp, ecx
  sbb esp, edx
  sbb esp, edi
  sbb esp, esi
  sbb esp, ebp
  sbb esp, esp
  sbb esp, r8d
  sbb esp, r9d
  sbb esp, r10d
  sbb esp, r11d
  sbb esp, r12d
  sbb esp, r13d
  sbb esp, r14d
  sbb esp, r15d
  sbb r8d, eax
  sbb r8d, ebx
  sbb r8d, ecx
  sbb r8d, edx
  sbb r8d, edi
  sbb r8d, esi
  sbb r8d, ebp
  sbb r8d, esp
  sbb r8d, r8d
  sbb r8d, r9d
  sbb r8d, r10d
  sbb r8d, r11d
  sbb r8d, r12d
  sbb r8d, r13d
  sbb r8d, r14d
  sbb r8d, r15d
  sbb r9d, eax
  sbb r9d, ebx
  sbb r9d, ecx
  sbb r9d, edx
  sbb r9d, edi
  sbb r9d, esi
  sbb r9d, ebp
  sbb r9d, esp
  sbb r9d, r8d
  sbb r9d, r9d
  sbb r9d, r10d
  sbb r9d, r11d
  sbb r9d, r12d
  sbb r9d, r13d
  sbb r9d, r14d
  sbb r9d, r15d
  sbb r10d, eax
  sbb r10d, ebx
  sbb r10d, ecx
  sbb r10d, edx
  sbb r10d, edi
  sbb r10d, esi
  sbb r10d, ebp
  sbb r10d, esp
  sbb r10d, r8d
  sbb r10d, r9d
  sbb r10d, r10d
  sbb r10d, r11d
  sbb r10d, r12d
  sbb r10d, r13d
  sbb r10d, r14d
  sbb r10d, r15d
  sbb r11d, eax
  sbb r11d, ebx
  sbb r11d, ecx
  sbb r11d, edx
  sbb r11d, edi
  sbb r11d, esi
  sbb r11d, ebp
  sbb r11d, esp
  sbb r11d, r8d
  sbb r11d, r9d
  sbb r11d, r10d
  sbb r11d, r11d
  sbb r11d, r12d
  sbb r11d, r13d
  sbb r11d, r14d
  sbb r11d, r15d
  sbb r12d, eax
  sbb r12d, ebx
  sbb r12d, ecx
  sbb r12d, edx
  sbb r12d, edi
  sbb r12d, esi
  sbb r12d, ebp
  sbb r12d, esp
  sbb r12d, r8d
  sbb r12d, r9d
  sbb r12d, r10d
  sbb r12d, r11d
  sbb r12d, r12d
  sbb r12d, r13d
  sbb r12d, r14d
  sbb r12d, r15d
  sbb r13d, eax
  sbb r13d, ebx
  sbb r13d, ecx
  sbb r13d, edx
  sbb r13d, edi
  sbb r13d, esi
  sbb r13d, ebp
  sbb r13d, esp
  sbb r13d, r8d
  sbb r13d, r9d
  sbb r13d, r10d
  sbb r13d, r11d
  sbb r13d, r12d
  sbb r13d, r13d
  sbb r13d, r14d
  sbb r13d, r15d
  sbb r14d, eax
  sbb r14d, ebx
  sbb r14d, ecx
  sbb r14d, edx
  sbb r14d, edi
  sbb r14d, esi
  sbb r14d, ebp
  sbb r14d, esp
  sbb r14d, r8d
  sbb r14d, r9d
  sbb r14d, r10d
  sbb r14d, r11d
  sbb r14d, r12d
  sbb r14d, r13d
  sbb r14d, r14d
  sbb r14d, r15d
  sbb r15d, eax
  sbb r15d, ebx
  sbb r15d, ecx
  sbb r15d, edx
  sbb r15d, edi
  sbb r15d, esi
  sbb r15d, ebp
  sbb r15d, esp
  sbb r15d, r8d
  sbb r15d, r9d
  sbb r15d, r10d
  sbb r15d, r11d
  sbb r15d, r12d
  sbb r15d, r13d
  sbb r15d, r14d
  sbb r15d, r15d


; sbb m32,r32

  sbb dword [mem32], eax
  sbb dword [mem32], ebx
  sbb dword [mem32], ecx
  sbb dword [mem32], edx
  sbb dword [mem32], edi
  sbb dword [mem32], esi
  sbb dword [mem32], ebp
  sbb dword [mem32], esp
  sbb dword [mem32], r8d
  sbb dword [mem32], r9d
  sbb dword [mem32], r10d
  sbb dword [mem32], r11d
  sbb dword [mem32], r12d
  sbb dword [mem32], r13d
  sbb dword [mem32], r14d
  sbb dword [mem32], r15d


; sbb r32,m32

  sbb eax, dword [mem32]
  sbb ebx, dword [mem32]
  sbb ecx, dword [mem32]
  sbb edx, dword [mem32]
  sbb edi, dword [mem32]
  sbb esi, dword [mem32]
  sbb ebp, dword [mem32]
  sbb esp, dword [mem32]
  sbb r8d, dword [mem32]
  sbb r9d, dword [mem32]
  sbb r10d, dword [mem32]
  sbb r11d, dword [mem32]
  sbb r12d, dword [mem32]
  sbb r13d, dword [mem32]
  sbb r14d, dword [mem32]
  sbb r15d, dword [mem32]


; sbb r32,i32

  sbb eax, imm32
  sbb ebx, imm32
  sbb ecx, imm32
  sbb edx, imm32
  sbb edi, imm32
  sbb esi, imm32
  sbb ebp, imm32
  sbb esp, imm32
  sbb r8d, imm32
  sbb r9d, imm32
  sbb r10d, imm32
  sbb r11d, imm32
  sbb r12d, imm32
  sbb r13d, imm32
  sbb r14d, imm32
  sbb r15d, imm32


; sbb m32,i32

  sbb dword [mem32], imm32


; sbb r64,r64

  sbb rax, rax
  sbb rax, rbx
  sbb rax, rcx
  sbb rax, rdx
  sbb rax, rdi
  sbb rax, rsi
  sbb rax, rbp
  sbb rax, rsp
  sbb rax, r8
  sbb rax, r9
  sbb rax, r10
  sbb rax, r11
  sbb rax, r12
  sbb rax, r13
  sbb rax, r14
  sbb rax, r15
  sbb rbx, rax
  sbb rbx, rbx
  sbb rbx, rcx
  sbb rbx, rdx
  sbb rbx, rdi
  sbb rbx, rsi
  sbb rbx, rbp
  sbb rbx, rsp
  sbb rbx, r8
  sbb rbx, r9
  sbb rbx, r10
  sbb rbx, r11
  sbb rbx, r12
  sbb rbx, r13
  sbb rbx, r14
  sbb rbx, r15
  sbb rcx, rax
  sbb rcx, rbx
  sbb rcx, rcx
  sbb rcx, rdx
  sbb rcx, rdi
  sbb rcx, rsi
  sbb rcx, rbp
  sbb rcx, rsp
  sbb rcx, r8
  sbb rcx, r9
  sbb rcx, r10
  sbb rcx, r11
  sbb rcx, r12
  sbb rcx, r13
  sbb rcx, r14
  sbb rcx, r15
  sbb rdx, rax
  sbb rdx, rbx
  sbb rdx, rcx
  sbb rdx, rdx
  sbb rdx, rdi
  sbb rdx, rsi
  sbb rdx, rbp
  sbb rdx, rsp
  sbb rdx, r8
  sbb rdx, r9
  sbb rdx, r10
  sbb rdx, r11
  sbb rdx, r12
  sbb rdx, r13
  sbb rdx, r14
  sbb rdx, r15
  sbb rdi, rax
  sbb rdi, rbx
  sbb rdi, rcx
  sbb rdi, rdx
  sbb rdi, rdi
  sbb rdi, rsi
  sbb rdi, rbp
  sbb rdi, rsp
  sbb rdi, r8
  sbb rdi, r9
  sbb rdi, r10
  sbb rdi, r11
  sbb rdi, r12
  sbb rdi, r13
  sbb rdi, r14
  sbb rdi, r15
  sbb rsi, rax
  sbb rsi, rbx
  sbb rsi, rcx
  sbb rsi, rdx
  sbb rsi, rdi
  sbb rsi, rsi
  sbb rsi, rbp
  sbb rsi, rsp
  sbb rsi, r8
  sbb rsi, r9
  sbb rsi, r10
  sbb rsi, r11
  sbb rsi, r12
  sbb rsi, r13
  sbb rsi, r14
  sbb rsi, r15
  sbb rbp, rax
  sbb rbp, rbx
  sbb rbp, rcx
  sbb rbp, rdx
  sbb rbp, rdi
  sbb rbp, rsi
  sbb rbp, rbp
  sbb rbp, rsp
  sbb rbp, r8
  sbb rbp, r9
  sbb rbp, r10
  sbb rbp, r11
  sbb rbp, r12
  sbb rbp, r13
  sbb rbp, r14
  sbb rbp, r15
  sbb rsp, rax
  sbb rsp, rbx
  sbb rsp, rcx
  sbb rsp, rdx
  sbb rsp, rdi
  sbb rsp, rsi
  sbb rsp, rbp
  sbb rsp, rsp
  sbb rsp, r8
  sbb rsp, r9
  sbb rsp, r10
  sbb rsp, r11
  sbb rsp, r12
  sbb rsp, r13
  sbb rsp, r14
  sbb rsp, r15
  sbb r8, rax
  sbb r8, rbx
  sbb r8, rcx
  sbb r8, rdx
  sbb r8, rdi
  sbb r8, rsi
  sbb r8, rbp
  sbb r8, rsp
  sbb r8, r8
  sbb r8, r9
  sbb r8, r10
  sbb r8, r11
  sbb r8, r12
  sbb r8, r13
  sbb r8, r14
  sbb r8, r15
  sbb r9, rax
  sbb r9, rbx
  sbb r9, rcx
  sbb r9, rdx
  sbb r9, rdi
  sbb r9, rsi
  sbb r9, rbp
  sbb r9, rsp
  sbb r9, r8
  sbb r9, r9
  sbb r9, r10
  sbb r9, r11
  sbb r9, r12
  sbb r9, r13
  sbb r9, r14
  sbb r9, r15
  sbb r10, rax
  sbb r10, rbx
  sbb r10, rcx
  sbb r10, rdx
  sbb r10, rdi
  sbb r10, rsi
  sbb r10, rbp
  sbb r10, rsp
  sbb r10, r8
  sbb r10, r9
  sbb r10, r10
  sbb r10, r11
  sbb r10, r12
  sbb r10, r13
  sbb r10, r14
  sbb r10, r15
  sbb r11, rax
  sbb r11, rbx
  sbb r11, rcx
  sbb r11, rdx
  sbb r11, rdi
  sbb r11, rsi
  sbb r11, rbp
  sbb r11, rsp
  sbb r11, r8
  sbb r11, r9
  sbb r11, r10
  sbb r11, r11
  sbb r11, r12
  sbb r11, r13
  sbb r11, r14
  sbb r11, r15
  sbb r12, rax
  sbb r12, rbx
  sbb r12, rcx
  sbb r12, rdx
  sbb r12, rdi
  sbb r12, rsi
  sbb r12, rbp
  sbb r12, rsp
  sbb r12, r8
  sbb r12, r9
  sbb r12, r10
  sbb r12, r11
  sbb r12, r12
  sbb r12, r13
  sbb r12, r14
  sbb r12, r15
  sbb r13, rax
  sbb r13, rbx
  sbb r13, rcx
  sbb r13, rdx
  sbb r13, rdi
  sbb r13, rsi
  sbb r13, rbp
  sbb r13, rsp
  sbb r13, r8
  sbb r13, r9
  sbb r13, r10
  sbb r13, r11
  sbb r13, r12
  sbb r13, r13
  sbb r13, r14
  sbb r13, r15
  sbb r14, rax
  sbb r14, rbx
  sbb r14, rcx
  sbb r14, rdx
  sbb r14, rdi
  sbb r14, rsi
  sbb r14, rbp
  sbb r14, rsp
  sbb r14, r8
  sbb r14, r9
  sbb r14, r10
  sbb r14, r11
  sbb r14, r12
  sbb r14, r13
  sbb r14, r14
  sbb r14, r15
  sbb r15, rax
  sbb r15, rbx
  sbb r15, rcx
  sbb r15, rdx
  sbb r15, rdi
  sbb r15, rsi
  sbb r15, rbp
  sbb r15, rsp
  sbb r15, r8
  sbb r15, r9
  sbb r15, r10
  sbb r15, r11
  sbb r15, r12
  sbb r15, r13
  sbb r15, r14
  sbb r15, r15


; sbb m64,r64

  sbb qword [mem64], rax
  sbb qword [mem64], rbx
  sbb qword [mem64], rcx
  sbb qword [mem64], rdx
  sbb qword [mem64], rdi
  sbb qword [mem64], rsi
  sbb qword [mem64], rbp
  sbb qword [mem64], rsp
  sbb qword [mem64], r8
  sbb qword [mem64], r9
  sbb qword [mem64], r10
  sbb qword [mem64], r11
  sbb qword [mem64], r12
  sbb qword [mem64], r13
  sbb qword [mem64], r14
  sbb qword [mem64], r15


; sbb r64,m64

  sbb rax, qword [mem64]
  sbb rbx, qword [mem64]
  sbb rcx, qword [mem64]
  sbb rdx, qword [mem64]
  sbb rdi, qword [mem64]
  sbb rsi, qword [mem64]
  sbb rbp, qword [mem64]
  sbb rsp, qword [mem64]
  sbb r8, qword [mem64]
  sbb r9, qword [mem64]
  sbb r10, qword [mem64]
  sbb r11, qword [mem64]
  sbb r12, qword [mem64]
  sbb r13, qword [mem64]
  sbb r14, qword [mem64]
  sbb r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
