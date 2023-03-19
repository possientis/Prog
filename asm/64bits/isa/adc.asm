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

; adc r8,r8

  adc al, al
  adc al, bl
  adc al, cl
  adc al, dl
  adc al, dil
  adc al, sil
  adc al, bpl
  adc al, spl
  adc al, r8b
  adc al, r9b
  adc al, r10b
  adc al, r11b
  adc al, r12b
  adc al, r13b
  adc al, r14b
  adc al, r15b
  adc bl, al
  adc bl, bl
  adc bl, cl
  adc bl, dl
  adc bl, dil
  adc bl, sil
  adc bl, bpl
  adc bl, spl
  adc bl, r8b
  adc bl, r9b
  adc bl, r10b
  adc bl, r11b
  adc bl, r12b
  adc bl, r13b
  adc bl, r14b
  adc bl, r15b
  adc cl, al
  adc cl, bl
  adc cl, cl
  adc cl, dl
  adc cl, dil
  adc cl, sil
  adc cl, bpl
  adc cl, spl
  adc cl, r8b
  adc cl, r9b
  adc cl, r10b
  adc cl, r11b
  adc cl, r12b
  adc cl, r13b
  adc cl, r14b
  adc cl, r15b
  adc dl, al
  adc dl, bl
  adc dl, cl
  adc dl, dl
  adc dl, dil
  adc dl, sil
  adc dl, bpl
  adc dl, spl
  adc dl, r8b
  adc dl, r9b
  adc dl, r10b
  adc dl, r11b
  adc dl, r12b
  adc dl, r13b
  adc dl, r14b
  adc dl, r15b
  adc dil, al
  adc dil, bl
  adc dil, cl
  adc dil, dl
  adc dil, dil
  adc dil, sil
  adc dil, bpl
  adc dil, spl
  adc dil, r8b
  adc dil, r9b
  adc dil, r10b
  adc dil, r11b
  adc dil, r12b
  adc dil, r13b
  adc dil, r14b
  adc dil, r15b
  adc sil, al
  adc sil, bl
  adc sil, cl
  adc sil, dl
  adc sil, dil
  adc sil, sil
  adc sil, bpl
  adc sil, spl
  adc sil, r8b
  adc sil, r9b
  adc sil, r10b
  adc sil, r11b
  adc sil, r12b
  adc sil, r13b
  adc sil, r14b
  adc sil, r15b
  adc bpl, al
  adc bpl, bl
  adc bpl, cl
  adc bpl, dl
  adc bpl, dil
  adc bpl, sil
  adc bpl, bpl
  adc bpl, spl
  adc bpl, r8b
  adc bpl, r9b
  adc bpl, r10b
  adc bpl, r11b
  adc bpl, r12b
  adc bpl, r13b
  adc bpl, r14b
  adc bpl, r15b
  adc spl, al
  adc spl, bl
  adc spl, cl
  adc spl, dl
  adc spl, dil
  adc spl, sil
  adc spl, bpl
  adc spl, spl
  adc spl, r8b
  adc spl, r9b
  adc spl, r10b
  adc spl, r11b
  adc spl, r12b
  adc spl, r13b
  adc spl, r14b
  adc spl, r15b
  adc r8b, al
  adc r8b, bl
  adc r8b, cl
  adc r8b, dl
  adc r8b, dil
  adc r8b, sil
  adc r8b, bpl
  adc r8b, spl
  adc r8b, r8b
  adc r8b, r9b
  adc r8b, r10b
  adc r8b, r11b
  adc r8b, r12b
  adc r8b, r13b
  adc r8b, r14b
  adc r8b, r15b
  adc r9b, al
  adc r9b, bl
  adc r9b, cl
  adc r9b, dl
  adc r9b, dil
  adc r9b, sil
  adc r9b, bpl
  adc r9b, spl
  adc r9b, r8b
  adc r9b, r9b
  adc r9b, r10b
  adc r9b, r11b
  adc r9b, r12b
  adc r9b, r13b
  adc r9b, r14b
  adc r9b, r15b
  adc r10b, al
  adc r10b, bl
  adc r10b, cl
  adc r10b, dl
  adc r10b, dil
  adc r10b, sil
  adc r10b, bpl
  adc r10b, spl
  adc r10b, r8b
  adc r10b, r9b
  adc r10b, r10b
  adc r10b, r11b
  adc r10b, r12b
  adc r10b, r13b
  adc r10b, r14b
  adc r10b, r15b
  adc r11b, al
  adc r11b, bl
  adc r11b, cl
  adc r11b, dl
  adc r11b, dil
  adc r11b, sil
  adc r11b, bpl
  adc r11b, spl
  adc r11b, r8b
  adc r11b, r9b
  adc r11b, r10b
  adc r11b, r11b
  adc r11b, r12b
  adc r11b, r13b
  adc r11b, r14b
  adc r11b, r15b
  adc r12b, al
  adc r12b, bl
  adc r12b, cl
  adc r12b, dl
  adc r12b, dil
  adc r12b, sil
  adc r12b, bpl
  adc r12b, spl
  adc r12b, r8b
  adc r12b, r9b
  adc r12b, r10b
  adc r12b, r11b
  adc r12b, r12b
  adc r12b, r13b
  adc r12b, r14b
  adc r12b, r15b
  adc r13b, al
  adc r13b, bl
  adc r13b, cl
  adc r13b, dl
  adc r13b, dil
  adc r13b, sil
  adc r13b, bpl
  adc r13b, spl
  adc r13b, r8b
  adc r13b, r9b
  adc r13b, r10b
  adc r13b, r11b
  adc r13b, r12b
  adc r13b, r13b
  adc r13b, r14b
  adc r13b, r15b
  adc r14b, al
  adc r14b, bl
  adc r14b, cl
  adc r14b, dl
  adc r14b, dil
  adc r14b, sil
  adc r14b, bpl
  adc r14b, spl
  adc r14b, r8b
  adc r14b, r9b
  adc r14b, r10b
  adc r14b, r11b
  adc r14b, r12b
  adc r14b, r13b
  adc r14b, r14b
  adc r14b, r15b
  adc r15b, al
  adc r15b, bl
  adc r15b, cl
  adc r15b, dl
  adc r15b, dil
  adc r15b, sil
  adc r15b, bpl
  adc r15b, spl
  adc r15b, r8b
  adc r15b, r9b
  adc r15b, r10b
  adc r15b, r11b
  adc r15b, r12b
  adc r15b, r13b
  adc r15b, r14b
  adc r15b, r15b


; adc m8,r8

  adc byte [mem8], al
  adc byte [mem8], bl
  adc byte [mem8], cl
  adc byte [mem8], dl
  adc byte [mem8], dil
  adc byte [mem8], sil
  adc byte [mem8], bpl
  adc byte [mem8], spl
  adc byte [mem8], r8b
  adc byte [mem8], r9b
  adc byte [mem8], r10b
  adc byte [mem8], r11b
  adc byte [mem8], r12b
  adc byte [mem8], r13b
  adc byte [mem8], r14b
  adc byte [mem8], r15b


; adc r8,m8

  adc al, byte [mem8]
  adc bl, byte [mem8]
  adc cl, byte [mem8]
  adc dl, byte [mem8]
  adc dil, byte [mem8]
  adc sil, byte [mem8]
  adc bpl, byte [mem8]
  adc spl, byte [mem8]
  adc r8b, byte [mem8]
  adc r9b, byte [mem8]
  adc r10b, byte [mem8]
  adc r11b, byte [mem8]
  adc r12b, byte [mem8]
  adc r13b, byte [mem8]
  adc r14b, byte [mem8]
  adc r15b, byte [mem8]


; adc r8,i8

  adc al, imm8
  adc bl, imm8
  adc cl, imm8
  adc dl, imm8
  adc dil, imm8
  adc sil, imm8
  adc bpl, imm8
  adc spl, imm8
  adc r8b, imm8
  adc r9b, imm8
  adc r10b, imm8
  adc r11b, imm8
  adc r12b, imm8
  adc r13b, imm8
  adc r14b, imm8
  adc r15b, imm8


; adc m8,i8

  adc byte [mem8], imm8


; adc r16,r16

  adc ax, ax
  adc ax, bx
  adc ax, cx
  adc ax, dx
  adc ax, di
  adc ax, si
  adc ax, bp
  adc ax, sp
  adc ax, r8w
  adc ax, r9w
  adc ax, r10w
  adc ax, r11w
  adc ax, r12w
  adc ax, r13w
  adc ax, r14w
  adc ax, r15w
  adc bx, ax
  adc bx, bx
  adc bx, cx
  adc bx, dx
  adc bx, di
  adc bx, si
  adc bx, bp
  adc bx, sp
  adc bx, r8w
  adc bx, r9w
  adc bx, r10w
  adc bx, r11w
  adc bx, r12w
  adc bx, r13w
  adc bx, r14w
  adc bx, r15w
  adc cx, ax
  adc cx, bx
  adc cx, cx
  adc cx, dx
  adc cx, di
  adc cx, si
  adc cx, bp
  adc cx, sp
  adc cx, r8w
  adc cx, r9w
  adc cx, r10w
  adc cx, r11w
  adc cx, r12w
  adc cx, r13w
  adc cx, r14w
  adc cx, r15w
  adc dx, ax
  adc dx, bx
  adc dx, cx
  adc dx, dx
  adc dx, di
  adc dx, si
  adc dx, bp
  adc dx, sp
  adc dx, r8w
  adc dx, r9w
  adc dx, r10w
  adc dx, r11w
  adc dx, r12w
  adc dx, r13w
  adc dx, r14w
  adc dx, r15w
  adc di, ax
  adc di, bx
  adc di, cx
  adc di, dx
  adc di, di
  adc di, si
  adc di, bp
  adc di, sp
  adc di, r8w
  adc di, r9w
  adc di, r10w
  adc di, r11w
  adc di, r12w
  adc di, r13w
  adc di, r14w
  adc di, r15w
  adc si, ax
  adc si, bx
  adc si, cx
  adc si, dx
  adc si, di
  adc si, si
  adc si, bp
  adc si, sp
  adc si, r8w
  adc si, r9w
  adc si, r10w
  adc si, r11w
  adc si, r12w
  adc si, r13w
  adc si, r14w
  adc si, r15w
  adc bp, ax
  adc bp, bx
  adc bp, cx
  adc bp, dx
  adc bp, di
  adc bp, si
  adc bp, bp
  adc bp, sp
  adc bp, r8w
  adc bp, r9w
  adc bp, r10w
  adc bp, r11w
  adc bp, r12w
  adc bp, r13w
  adc bp, r14w
  adc bp, r15w
  adc sp, ax
  adc sp, bx
  adc sp, cx
  adc sp, dx
  adc sp, di
  adc sp, si
  adc sp, bp
  adc sp, sp
  adc sp, r8w
  adc sp, r9w
  adc sp, r10w
  adc sp, r11w
  adc sp, r12w
  adc sp, r13w
  adc sp, r14w
  adc sp, r15w
  adc r8w, ax
  adc r8w, bx
  adc r8w, cx
  adc r8w, dx
  adc r8w, di
  adc r8w, si
  adc r8w, bp
  adc r8w, sp
  adc r8w, r8w
  adc r8w, r9w
  adc r8w, r10w
  adc r8w, r11w
  adc r8w, r12w
  adc r8w, r13w
  adc r8w, r14w
  adc r8w, r15w
  adc r9w, ax
  adc r9w, bx
  adc r9w, cx
  adc r9w, dx
  adc r9w, di
  adc r9w, si
  adc r9w, bp
  adc r9w, sp
  adc r9w, r8w
  adc r9w, r9w
  adc r9w, r10w
  adc r9w, r11w
  adc r9w, r12w
  adc r9w, r13w
  adc r9w, r14w
  adc r9w, r15w
  adc r10w, ax
  adc r10w, bx
  adc r10w, cx
  adc r10w, dx
  adc r10w, di
  adc r10w, si
  adc r10w, bp
  adc r10w, sp
  adc r10w, r8w
  adc r10w, r9w
  adc r10w, r10w
  adc r10w, r11w
  adc r10w, r12w
  adc r10w, r13w
  adc r10w, r14w
  adc r10w, r15w
  adc r11w, ax
  adc r11w, bx
  adc r11w, cx
  adc r11w, dx
  adc r11w, di
  adc r11w, si
  adc r11w, bp
  adc r11w, sp
  adc r11w, r8w
  adc r11w, r9w
  adc r11w, r10w
  adc r11w, r11w
  adc r11w, r12w
  adc r11w, r13w
  adc r11w, r14w
  adc r11w, r15w
  adc r12w, ax
  adc r12w, bx
  adc r12w, cx
  adc r12w, dx
  adc r12w, di
  adc r12w, si
  adc r12w, bp
  adc r12w, sp
  adc r12w, r8w
  adc r12w, r9w
  adc r12w, r10w
  adc r12w, r11w
  adc r12w, r12w
  adc r12w, r13w
  adc r12w, r14w
  adc r12w, r15w
  adc r13w, ax
  adc r13w, bx
  adc r13w, cx
  adc r13w, dx
  adc r13w, di
  adc r13w, si
  adc r13w, bp
  adc r13w, sp
  adc r13w, r8w
  adc r13w, r9w
  adc r13w, r10w
  adc r13w, r11w
  adc r13w, r12w
  adc r13w, r13w
  adc r13w, r14w
  adc r13w, r15w
  adc r14w, ax
  adc r14w, bx
  adc r14w, cx
  adc r14w, dx
  adc r14w, di
  adc r14w, si
  adc r14w, bp
  adc r14w, sp
  adc r14w, r8w
  adc r14w, r9w
  adc r14w, r10w
  adc r14w, r11w
  adc r14w, r12w
  adc r14w, r13w
  adc r14w, r14w
  adc r14w, r15w
  adc r15w, ax
  adc r15w, bx
  adc r15w, cx
  adc r15w, dx
  adc r15w, di
  adc r15w, si
  adc r15w, bp
  adc r15w, sp
  adc r15w, r8w
  adc r15w, r9w
  adc r15w, r10w
  adc r15w, r11w
  adc r15w, r12w
  adc r15w, r13w
  adc r15w, r14w
  adc r15w, r15w


; adc m16,r16

  adc word [mem16], ax
  adc word [mem16], bx
  adc word [mem16], cx
  adc word [mem16], dx
  adc word [mem16], di
  adc word [mem16], si
  adc word [mem16], bp
  adc word [mem16], sp
  adc word [mem16], r8w
  adc word [mem16], r9w
  adc word [mem16], r10w
  adc word [mem16], r11w
  adc word [mem16], r12w
  adc word [mem16], r13w
  adc word [mem16], r14w
  adc word [mem16], r15w


; adc r16,m16

  adc ax, word [mem16]
  adc bx, word [mem16]
  adc cx, word [mem16]
  adc dx, word [mem16]
  adc di, word [mem16]
  adc si, word [mem16]
  adc bp, word [mem16]
  adc sp, word [mem16]
  adc r8w, word [mem16]
  adc r9w, word [mem16]
  adc r10w, word [mem16]
  adc r11w, word [mem16]
  adc r12w, word [mem16]
  adc r13w, word [mem16]
  adc r14w, word [mem16]
  adc r15w, word [mem16]


; adc r16,i16

  adc ax, imm16
  adc bx, imm16
  adc cx, imm16
  adc dx, imm16
  adc di, imm16
  adc si, imm16
  adc bp, imm16
  adc sp, imm16
  adc r8w, imm16
  adc r9w, imm16
  adc r10w, imm16
  adc r11w, imm16
  adc r12w, imm16
  adc r13w, imm16
  adc r14w, imm16
  adc r15w, imm16


; adc m16,i16

  adc word [mem16], imm16


; adc r32,r32

  adc eax, eax
  adc eax, ebx
  adc eax, ecx
  adc eax, edx
  adc eax, edi
  adc eax, esi
  adc eax, ebp
  adc eax, esp
  adc eax, r8d
  adc eax, r9d
  adc eax, r10d
  adc eax, r11d
  adc eax, r12d
  adc eax, r13d
  adc eax, r14d
  adc eax, r15d
  adc ebx, eax
  adc ebx, ebx
  adc ebx, ecx
  adc ebx, edx
  adc ebx, edi
  adc ebx, esi
  adc ebx, ebp
  adc ebx, esp
  adc ebx, r8d
  adc ebx, r9d
  adc ebx, r10d
  adc ebx, r11d
  adc ebx, r12d
  adc ebx, r13d
  adc ebx, r14d
  adc ebx, r15d
  adc ecx, eax
  adc ecx, ebx
  adc ecx, ecx
  adc ecx, edx
  adc ecx, edi
  adc ecx, esi
  adc ecx, ebp
  adc ecx, esp
  adc ecx, r8d
  adc ecx, r9d
  adc ecx, r10d
  adc ecx, r11d
  adc ecx, r12d
  adc ecx, r13d
  adc ecx, r14d
  adc ecx, r15d
  adc edx, eax
  adc edx, ebx
  adc edx, ecx
  adc edx, edx
  adc edx, edi
  adc edx, esi
  adc edx, ebp
  adc edx, esp
  adc edx, r8d
  adc edx, r9d
  adc edx, r10d
  adc edx, r11d
  adc edx, r12d
  adc edx, r13d
  adc edx, r14d
  adc edx, r15d
  adc edi, eax
  adc edi, ebx
  adc edi, ecx
  adc edi, edx
  adc edi, edi
  adc edi, esi
  adc edi, ebp
  adc edi, esp
  adc edi, r8d
  adc edi, r9d
  adc edi, r10d
  adc edi, r11d
  adc edi, r12d
  adc edi, r13d
  adc edi, r14d
  adc edi, r15d
  adc esi, eax
  adc esi, ebx
  adc esi, ecx
  adc esi, edx
  adc esi, edi
  adc esi, esi
  adc esi, ebp
  adc esi, esp
  adc esi, r8d
  adc esi, r9d
  adc esi, r10d
  adc esi, r11d
  adc esi, r12d
  adc esi, r13d
  adc esi, r14d
  adc esi, r15d
  adc ebp, eax
  adc ebp, ebx
  adc ebp, ecx
  adc ebp, edx
  adc ebp, edi
  adc ebp, esi
  adc ebp, ebp
  adc ebp, esp
  adc ebp, r8d
  adc ebp, r9d
  adc ebp, r10d
  adc ebp, r11d
  adc ebp, r12d
  adc ebp, r13d
  adc ebp, r14d
  adc ebp, r15d
  adc esp, eax
  adc esp, ebx
  adc esp, ecx
  adc esp, edx
  adc esp, edi
  adc esp, esi
  adc esp, ebp
  adc esp, esp
  adc esp, r8d
  adc esp, r9d
  adc esp, r10d
  adc esp, r11d
  adc esp, r12d
  adc esp, r13d
  adc esp, r14d
  adc esp, r15d
  adc r8d, eax
  adc r8d, ebx
  adc r8d, ecx
  adc r8d, edx
  adc r8d, edi
  adc r8d, esi
  adc r8d, ebp
  adc r8d, esp
  adc r8d, r8d
  adc r8d, r9d
  adc r8d, r10d
  adc r8d, r11d
  adc r8d, r12d
  adc r8d, r13d
  adc r8d, r14d
  adc r8d, r15d
  adc r9d, eax
  adc r9d, ebx
  adc r9d, ecx
  adc r9d, edx
  adc r9d, edi
  adc r9d, esi
  adc r9d, ebp
  adc r9d, esp
  adc r9d, r8d
  adc r9d, r9d
  adc r9d, r10d
  adc r9d, r11d
  adc r9d, r12d
  adc r9d, r13d
  adc r9d, r14d
  adc r9d, r15d
  adc r10d, eax
  adc r10d, ebx
  adc r10d, ecx
  adc r10d, edx
  adc r10d, edi
  adc r10d, esi
  adc r10d, ebp
  adc r10d, esp
  adc r10d, r8d
  adc r10d, r9d
  adc r10d, r10d
  adc r10d, r11d
  adc r10d, r12d
  adc r10d, r13d
  adc r10d, r14d
  adc r10d, r15d
  adc r11d, eax
  adc r11d, ebx
  adc r11d, ecx
  adc r11d, edx
  adc r11d, edi
  adc r11d, esi
  adc r11d, ebp
  adc r11d, esp
  adc r11d, r8d
  adc r11d, r9d
  adc r11d, r10d
  adc r11d, r11d
  adc r11d, r12d
  adc r11d, r13d
  adc r11d, r14d
  adc r11d, r15d
  adc r12d, eax
  adc r12d, ebx
  adc r12d, ecx
  adc r12d, edx
  adc r12d, edi
  adc r12d, esi
  adc r12d, ebp
  adc r12d, esp
  adc r12d, r8d
  adc r12d, r9d
  adc r12d, r10d
  adc r12d, r11d
  adc r12d, r12d
  adc r12d, r13d
  adc r12d, r14d
  adc r12d, r15d
  adc r13d, eax
  adc r13d, ebx
  adc r13d, ecx
  adc r13d, edx
  adc r13d, edi
  adc r13d, esi
  adc r13d, ebp
  adc r13d, esp
  adc r13d, r8d
  adc r13d, r9d
  adc r13d, r10d
  adc r13d, r11d
  adc r13d, r12d
  adc r13d, r13d
  adc r13d, r14d
  adc r13d, r15d
  adc r14d, eax
  adc r14d, ebx
  adc r14d, ecx
  adc r14d, edx
  adc r14d, edi
  adc r14d, esi
  adc r14d, ebp
  adc r14d, esp
  adc r14d, r8d
  adc r14d, r9d
  adc r14d, r10d
  adc r14d, r11d
  adc r14d, r12d
  adc r14d, r13d
  adc r14d, r14d
  adc r14d, r15d
  adc r15d, eax
  adc r15d, ebx
  adc r15d, ecx
  adc r15d, edx
  adc r15d, edi
  adc r15d, esi
  adc r15d, ebp
  adc r15d, esp
  adc r15d, r8d
  adc r15d, r9d
  adc r15d, r10d
  adc r15d, r11d
  adc r15d, r12d
  adc r15d, r13d
  adc r15d, r14d
  adc r15d, r15d


; adc m32,r32

  adc dword [mem32], eax
  adc dword [mem32], ebx
  adc dword [mem32], ecx
  adc dword [mem32], edx
  adc dword [mem32], edi
  adc dword [mem32], esi
  adc dword [mem32], ebp
  adc dword [mem32], esp
  adc dword [mem32], r8d
  adc dword [mem32], r9d
  adc dword [mem32], r10d
  adc dword [mem32], r11d
  adc dword [mem32], r12d
  adc dword [mem32], r13d
  adc dword [mem32], r14d
  adc dword [mem32], r15d


; adc r32,m32

  adc eax, dword [mem32]
  adc ebx, dword [mem32]
  adc ecx, dword [mem32]
  adc edx, dword [mem32]
  adc edi, dword [mem32]
  adc esi, dword [mem32]
  adc ebp, dword [mem32]
  adc esp, dword [mem32]
  adc r8d, dword [mem32]
  adc r9d, dword [mem32]
  adc r10d, dword [mem32]
  adc r11d, dword [mem32]
  adc r12d, dword [mem32]
  adc r13d, dword [mem32]
  adc r14d, dword [mem32]
  adc r15d, dword [mem32]


; adc r32,i32

  adc eax, imm32
  adc ebx, imm32
  adc ecx, imm32
  adc edx, imm32
  adc edi, imm32
  adc esi, imm32
  adc ebp, imm32
  adc esp, imm32
  adc r8d, imm32
  adc r9d, imm32
  adc r10d, imm32
  adc r11d, imm32
  adc r12d, imm32
  adc r13d, imm32
  adc r14d, imm32
  adc r15d, imm32


; adc m32,i32

  adc dword [mem32], imm32


; adc r64,r64

  adc rax, rax
  adc rax, rbx
  adc rax, rcx
  adc rax, rdx
  adc rax, rdi
  adc rax, rsi
  adc rax, rbp
  adc rax, rsp
  adc rax, r8
  adc rax, r9
  adc rax, r10
  adc rax, r11
  adc rax, r12
  adc rax, r13
  adc rax, r14
  adc rax, r15
  adc rbx, rax
  adc rbx, rbx
  adc rbx, rcx
  adc rbx, rdx
  adc rbx, rdi
  adc rbx, rsi
  adc rbx, rbp
  adc rbx, rsp
  adc rbx, r8
  adc rbx, r9
  adc rbx, r10
  adc rbx, r11
  adc rbx, r12
  adc rbx, r13
  adc rbx, r14
  adc rbx, r15
  adc rcx, rax
  adc rcx, rbx
  adc rcx, rcx
  adc rcx, rdx
  adc rcx, rdi
  adc rcx, rsi
  adc rcx, rbp
  adc rcx, rsp
  adc rcx, r8
  adc rcx, r9
  adc rcx, r10
  adc rcx, r11
  adc rcx, r12
  adc rcx, r13
  adc rcx, r14
  adc rcx, r15
  adc rdx, rax
  adc rdx, rbx
  adc rdx, rcx
  adc rdx, rdx
  adc rdx, rdi
  adc rdx, rsi
  adc rdx, rbp
  adc rdx, rsp
  adc rdx, r8
  adc rdx, r9
  adc rdx, r10
  adc rdx, r11
  adc rdx, r12
  adc rdx, r13
  adc rdx, r14
  adc rdx, r15
  adc rdi, rax
  adc rdi, rbx
  adc rdi, rcx
  adc rdi, rdx
  adc rdi, rdi
  adc rdi, rsi
  adc rdi, rbp
  adc rdi, rsp
  adc rdi, r8
  adc rdi, r9
  adc rdi, r10
  adc rdi, r11
  adc rdi, r12
  adc rdi, r13
  adc rdi, r14
  adc rdi, r15
  adc rsi, rax
  adc rsi, rbx
  adc rsi, rcx
  adc rsi, rdx
  adc rsi, rdi
  adc rsi, rsi
  adc rsi, rbp
  adc rsi, rsp
  adc rsi, r8
  adc rsi, r9
  adc rsi, r10
  adc rsi, r11
  adc rsi, r12
  adc rsi, r13
  adc rsi, r14
  adc rsi, r15
  adc rbp, rax
  adc rbp, rbx
  adc rbp, rcx
  adc rbp, rdx
  adc rbp, rdi
  adc rbp, rsi
  adc rbp, rbp
  adc rbp, rsp
  adc rbp, r8
  adc rbp, r9
  adc rbp, r10
  adc rbp, r11
  adc rbp, r12
  adc rbp, r13
  adc rbp, r14
  adc rbp, r15
  adc rsp, rax
  adc rsp, rbx
  adc rsp, rcx
  adc rsp, rdx
  adc rsp, rdi
  adc rsp, rsi
  adc rsp, rbp
  adc rsp, rsp
  adc rsp, r8
  adc rsp, r9
  adc rsp, r10
  adc rsp, r11
  adc rsp, r12
  adc rsp, r13
  adc rsp, r14
  adc rsp, r15
  adc r8, rax
  adc r8, rbx
  adc r8, rcx
  adc r8, rdx
  adc r8, rdi
  adc r8, rsi
  adc r8, rbp
  adc r8, rsp
  adc r8, r8
  adc r8, r9
  adc r8, r10
  adc r8, r11
  adc r8, r12
  adc r8, r13
  adc r8, r14
  adc r8, r15
  adc r9, rax
  adc r9, rbx
  adc r9, rcx
  adc r9, rdx
  adc r9, rdi
  adc r9, rsi
  adc r9, rbp
  adc r9, rsp
  adc r9, r8
  adc r9, r9
  adc r9, r10
  adc r9, r11
  adc r9, r12
  adc r9, r13
  adc r9, r14
  adc r9, r15
  adc r10, rax
  adc r10, rbx
  adc r10, rcx
  adc r10, rdx
  adc r10, rdi
  adc r10, rsi
  adc r10, rbp
  adc r10, rsp
  adc r10, r8
  adc r10, r9
  adc r10, r10
  adc r10, r11
  adc r10, r12
  adc r10, r13
  adc r10, r14
  adc r10, r15
  adc r11, rax
  adc r11, rbx
  adc r11, rcx
  adc r11, rdx
  adc r11, rdi
  adc r11, rsi
  adc r11, rbp
  adc r11, rsp
  adc r11, r8
  adc r11, r9
  adc r11, r10
  adc r11, r11
  adc r11, r12
  adc r11, r13
  adc r11, r14
  adc r11, r15
  adc r12, rax
  adc r12, rbx
  adc r12, rcx
  adc r12, rdx
  adc r12, rdi
  adc r12, rsi
  adc r12, rbp
  adc r12, rsp
  adc r12, r8
  adc r12, r9
  adc r12, r10
  adc r12, r11
  adc r12, r12
  adc r12, r13
  adc r12, r14
  adc r12, r15
  adc r13, rax
  adc r13, rbx
  adc r13, rcx
  adc r13, rdx
  adc r13, rdi
  adc r13, rsi
  adc r13, rbp
  adc r13, rsp
  adc r13, r8
  adc r13, r9
  adc r13, r10
  adc r13, r11
  adc r13, r12
  adc r13, r13
  adc r13, r14
  adc r13, r15
  adc r14, rax
  adc r14, rbx
  adc r14, rcx
  adc r14, rdx
  adc r14, rdi
  adc r14, rsi
  adc r14, rbp
  adc r14, rsp
  adc r14, r8
  adc r14, r9
  adc r14, r10
  adc r14, r11
  adc r14, r12
  adc r14, r13
  adc r14, r14
  adc r14, r15
  adc r15, rax
  adc r15, rbx
  adc r15, rcx
  adc r15, rdx
  adc r15, rdi
  adc r15, rsi
  adc r15, rbp
  adc r15, rsp
  adc r15, r8
  adc r15, r9
  adc r15, r10
  adc r15, r11
  adc r15, r12
  adc r15, r13
  adc r15, r14
  adc r15, r15


; adc m64,r64

  adc qword [mem64], rax
  adc qword [mem64], rbx
  adc qword [mem64], rcx
  adc qword [mem64], rdx
  adc qword [mem64], rdi
  adc qword [mem64], rsi
  adc qword [mem64], rbp
  adc qword [mem64], rsp
  adc qword [mem64], r8
  adc qword [mem64], r9
  adc qword [mem64], r10
  adc qword [mem64], r11
  adc qword [mem64], r12
  adc qword [mem64], r13
  adc qword [mem64], r14
  adc qword [mem64], r15


; adc r64,m64

  adc rax, qword [mem64]
  adc rbx, qword [mem64]
  adc rcx, qword [mem64]
  adc rdx, qword [mem64]
  adc rdi, qword [mem64]
  adc rsi, qword [mem64]
  adc rbp, qword [mem64]
  adc rsp, qword [mem64]
  adc r8, qword [mem64]
  adc r9, qword [mem64]
  adc r10, qword [mem64]
  adc r11, qword [mem64]
  adc r12, qword [mem64]
  adc r13, qword [mem64]
  adc r14, qword [mem64]
  adc r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
