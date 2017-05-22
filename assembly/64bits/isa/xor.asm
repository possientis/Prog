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

; xor r8,r8

  xor al, al
  xor al, bl
  xor al, cl
  xor al, dl
  xor al, dil
  xor al, sil
  xor al, bpl
  xor al, spl
  xor al, r8b
  xor al, r9b
  xor al, r10b
  xor al, r11b
  xor al, r12b
  xor al, r13b
  xor al, r14b
  xor al, r15b
  xor bl, al
  xor bl, bl
  xor bl, cl
  xor bl, dl
  xor bl, dil
  xor bl, sil
  xor bl, bpl
  xor bl, spl
  xor bl, r8b
  xor bl, r9b
  xor bl, r10b
  xor bl, r11b
  xor bl, r12b
  xor bl, r13b
  xor bl, r14b
  xor bl, r15b
  xor cl, al
  xor cl, bl
  xor cl, cl
  xor cl, dl
  xor cl, dil
  xor cl, sil
  xor cl, bpl
  xor cl, spl
  xor cl, r8b
  xor cl, r9b
  xor cl, r10b
  xor cl, r11b
  xor cl, r12b
  xor cl, r13b
  xor cl, r14b
  xor cl, r15b
  xor dl, al
  xor dl, bl
  xor dl, cl
  xor dl, dl
  xor dl, dil
  xor dl, sil
  xor dl, bpl
  xor dl, spl
  xor dl, r8b
  xor dl, r9b
  xor dl, r10b
  xor dl, r11b
  xor dl, r12b
  xor dl, r13b
  xor dl, r14b
  xor dl, r15b
  xor dil, al
  xor dil, bl
  xor dil, cl
  xor dil, dl
  xor dil, dil
  xor dil, sil
  xor dil, bpl
  xor dil, spl
  xor dil, r8b
  xor dil, r9b
  xor dil, r10b
  xor dil, r11b
  xor dil, r12b
  xor dil, r13b
  xor dil, r14b
  xor dil, r15b
  xor sil, al
  xor sil, bl
  xor sil, cl
  xor sil, dl
  xor sil, dil
  xor sil, sil
  xor sil, bpl
  xor sil, spl
  xor sil, r8b
  xor sil, r9b
  xor sil, r10b
  xor sil, r11b
  xor sil, r12b
  xor sil, r13b
  xor sil, r14b
  xor sil, r15b
  xor bpl, al
  xor bpl, bl
  xor bpl, cl
  xor bpl, dl
  xor bpl, dil
  xor bpl, sil
  xor bpl, bpl
  xor bpl, spl
  xor bpl, r8b
  xor bpl, r9b
  xor bpl, r10b
  xor bpl, r11b
  xor bpl, r12b
  xor bpl, r13b
  xor bpl, r14b
  xor bpl, r15b
  xor spl, al
  xor spl, bl
  xor spl, cl
  xor spl, dl
  xor spl, dil
  xor spl, sil
  xor spl, bpl
  xor spl, spl
  xor spl, r8b
  xor spl, r9b
  xor spl, r10b
  xor spl, r11b
  xor spl, r12b
  xor spl, r13b
  xor spl, r14b
  xor spl, r15b
  xor r8b, al
  xor r8b, bl
  xor r8b, cl
  xor r8b, dl
  xor r8b, dil
  xor r8b, sil
  xor r8b, bpl
  xor r8b, spl
  xor r8b, r8b
  xor r8b, r9b
  xor r8b, r10b
  xor r8b, r11b
  xor r8b, r12b
  xor r8b, r13b
  xor r8b, r14b
  xor r8b, r15b
  xor r9b, al
  xor r9b, bl
  xor r9b, cl
  xor r9b, dl
  xor r9b, dil
  xor r9b, sil
  xor r9b, bpl
  xor r9b, spl
  xor r9b, r8b
  xor r9b, r9b
  xor r9b, r10b
  xor r9b, r11b
  xor r9b, r12b
  xor r9b, r13b
  xor r9b, r14b
  xor r9b, r15b
  xor r10b, al
  xor r10b, bl
  xor r10b, cl
  xor r10b, dl
  xor r10b, dil
  xor r10b, sil
  xor r10b, bpl
  xor r10b, spl
  xor r10b, r8b
  xor r10b, r9b
  xor r10b, r10b
  xor r10b, r11b
  xor r10b, r12b
  xor r10b, r13b
  xor r10b, r14b
  xor r10b, r15b
  xor r11b, al
  xor r11b, bl
  xor r11b, cl
  xor r11b, dl
  xor r11b, dil
  xor r11b, sil
  xor r11b, bpl
  xor r11b, spl
  xor r11b, r8b
  xor r11b, r9b
  xor r11b, r10b
  xor r11b, r11b
  xor r11b, r12b
  xor r11b, r13b
  xor r11b, r14b
  xor r11b, r15b
  xor r12b, al
  xor r12b, bl
  xor r12b, cl
  xor r12b, dl
  xor r12b, dil
  xor r12b, sil
  xor r12b, bpl
  xor r12b, spl
  xor r12b, r8b
  xor r12b, r9b
  xor r12b, r10b
  xor r12b, r11b
  xor r12b, r12b
  xor r12b, r13b
  xor r12b, r14b
  xor r12b, r15b
  xor r13b, al
  xor r13b, bl
  xor r13b, cl
  xor r13b, dl
  xor r13b, dil
  xor r13b, sil
  xor r13b, bpl
  xor r13b, spl
  xor r13b, r8b
  xor r13b, r9b
  xor r13b, r10b
  xor r13b, r11b
  xor r13b, r12b
  xor r13b, r13b
  xor r13b, r14b
  xor r13b, r15b
  xor r14b, al
  xor r14b, bl
  xor r14b, cl
  xor r14b, dl
  xor r14b, dil
  xor r14b, sil
  xor r14b, bpl
  xor r14b, spl
  xor r14b, r8b
  xor r14b, r9b
  xor r14b, r10b
  xor r14b, r11b
  xor r14b, r12b
  xor r14b, r13b
  xor r14b, r14b
  xor r14b, r15b
  xor r15b, al
  xor r15b, bl
  xor r15b, cl
  xor r15b, dl
  xor r15b, dil
  xor r15b, sil
  xor r15b, bpl
  xor r15b, spl
  xor r15b, r8b
  xor r15b, r9b
  xor r15b, r10b
  xor r15b, r11b
  xor r15b, r12b
  xor r15b, r13b
  xor r15b, r14b
  xor r15b, r15b


; xor m8,r8

  xor byte [mem8], al
  xor byte [mem8], bl
  xor byte [mem8], cl
  xor byte [mem8], dl
  xor byte [mem8], dil
  xor byte [mem8], sil
  xor byte [mem8], bpl
  xor byte [mem8], spl
  xor byte [mem8], r8b
  xor byte [mem8], r9b
  xor byte [mem8], r10b
  xor byte [mem8], r11b
  xor byte [mem8], r12b
  xor byte [mem8], r13b
  xor byte [mem8], r14b
  xor byte [mem8], r15b


; xor r8,m8

  xor al, byte [mem8]
  xor bl, byte [mem8]
  xor cl, byte [mem8]
  xor dl, byte [mem8]
  xor dil, byte [mem8]
  xor sil, byte [mem8]
  xor bpl, byte [mem8]
  xor spl, byte [mem8]
  xor r8b, byte [mem8]
  xor r9b, byte [mem8]
  xor r10b, byte [mem8]
  xor r11b, byte [mem8]
  xor r12b, byte [mem8]
  xor r13b, byte [mem8]
  xor r14b, byte [mem8]
  xor r15b, byte [mem8]


; xor r8,i8

  xor al, imm8
  xor bl, imm8
  xor cl, imm8
  xor dl, imm8
  xor dil, imm8
  xor sil, imm8
  xor bpl, imm8
  xor spl, imm8
  xor r8b, imm8
  xor r9b, imm8
  xor r10b, imm8
  xor r11b, imm8
  xor r12b, imm8
  xor r13b, imm8
  xor r14b, imm8
  xor r15b, imm8


; xor m8,i8

  xor byte [mem8], imm8


; xor r16,r16

  xor ax, ax
  xor ax, bx
  xor ax, cx
  xor ax, dx
  xor ax, di
  xor ax, si
  xor ax, bp
  xor ax, sp
  xor ax, r8w
  xor ax, r9w
  xor ax, r10w
  xor ax, r11w
  xor ax, r12w
  xor ax, r13w
  xor ax, r14w
  xor ax, r15w
  xor bx, ax
  xor bx, bx
  xor bx, cx
  xor bx, dx
  xor bx, di
  xor bx, si
  xor bx, bp
  xor bx, sp
  xor bx, r8w
  xor bx, r9w
  xor bx, r10w
  xor bx, r11w
  xor bx, r12w
  xor bx, r13w
  xor bx, r14w
  xor bx, r15w
  xor cx, ax
  xor cx, bx
  xor cx, cx
  xor cx, dx
  xor cx, di
  xor cx, si
  xor cx, bp
  xor cx, sp
  xor cx, r8w
  xor cx, r9w
  xor cx, r10w
  xor cx, r11w
  xor cx, r12w
  xor cx, r13w
  xor cx, r14w
  xor cx, r15w
  xor dx, ax
  xor dx, bx
  xor dx, cx
  xor dx, dx
  xor dx, di
  xor dx, si
  xor dx, bp
  xor dx, sp
  xor dx, r8w
  xor dx, r9w
  xor dx, r10w
  xor dx, r11w
  xor dx, r12w
  xor dx, r13w
  xor dx, r14w
  xor dx, r15w
  xor di, ax
  xor di, bx
  xor di, cx
  xor di, dx
  xor di, di
  xor di, si
  xor di, bp
  xor di, sp
  xor di, r8w
  xor di, r9w
  xor di, r10w
  xor di, r11w
  xor di, r12w
  xor di, r13w
  xor di, r14w
  xor di, r15w
  xor si, ax
  xor si, bx
  xor si, cx
  xor si, dx
  xor si, di
  xor si, si
  xor si, bp
  xor si, sp
  xor si, r8w
  xor si, r9w
  xor si, r10w
  xor si, r11w
  xor si, r12w
  xor si, r13w
  xor si, r14w
  xor si, r15w
  xor bp, ax
  xor bp, bx
  xor bp, cx
  xor bp, dx
  xor bp, di
  xor bp, si
  xor bp, bp
  xor bp, sp
  xor bp, r8w
  xor bp, r9w
  xor bp, r10w
  xor bp, r11w
  xor bp, r12w
  xor bp, r13w
  xor bp, r14w
  xor bp, r15w
  xor sp, ax
  xor sp, bx
  xor sp, cx
  xor sp, dx
  xor sp, di
  xor sp, si
  xor sp, bp
  xor sp, sp
  xor sp, r8w
  xor sp, r9w
  xor sp, r10w
  xor sp, r11w
  xor sp, r12w
  xor sp, r13w
  xor sp, r14w
  xor sp, r15w
  xor r8w, ax
  xor r8w, bx
  xor r8w, cx
  xor r8w, dx
  xor r8w, di
  xor r8w, si
  xor r8w, bp
  xor r8w, sp
  xor r8w, r8w
  xor r8w, r9w
  xor r8w, r10w
  xor r8w, r11w
  xor r8w, r12w
  xor r8w, r13w
  xor r8w, r14w
  xor r8w, r15w
  xor r9w, ax
  xor r9w, bx
  xor r9w, cx
  xor r9w, dx
  xor r9w, di
  xor r9w, si
  xor r9w, bp
  xor r9w, sp
  xor r9w, r8w
  xor r9w, r9w
  xor r9w, r10w
  xor r9w, r11w
  xor r9w, r12w
  xor r9w, r13w
  xor r9w, r14w
  xor r9w, r15w
  xor r10w, ax
  xor r10w, bx
  xor r10w, cx
  xor r10w, dx
  xor r10w, di
  xor r10w, si
  xor r10w, bp
  xor r10w, sp
  xor r10w, r8w
  xor r10w, r9w
  xor r10w, r10w
  xor r10w, r11w
  xor r10w, r12w
  xor r10w, r13w
  xor r10w, r14w
  xor r10w, r15w
  xor r11w, ax
  xor r11w, bx
  xor r11w, cx
  xor r11w, dx
  xor r11w, di
  xor r11w, si
  xor r11w, bp
  xor r11w, sp
  xor r11w, r8w
  xor r11w, r9w
  xor r11w, r10w
  xor r11w, r11w
  xor r11w, r12w
  xor r11w, r13w
  xor r11w, r14w
  xor r11w, r15w
  xor r12w, ax
  xor r12w, bx
  xor r12w, cx
  xor r12w, dx
  xor r12w, di
  xor r12w, si
  xor r12w, bp
  xor r12w, sp
  xor r12w, r8w
  xor r12w, r9w
  xor r12w, r10w
  xor r12w, r11w
  xor r12w, r12w
  xor r12w, r13w
  xor r12w, r14w
  xor r12w, r15w
  xor r13w, ax
  xor r13w, bx
  xor r13w, cx
  xor r13w, dx
  xor r13w, di
  xor r13w, si
  xor r13w, bp
  xor r13w, sp
  xor r13w, r8w
  xor r13w, r9w
  xor r13w, r10w
  xor r13w, r11w
  xor r13w, r12w
  xor r13w, r13w
  xor r13w, r14w
  xor r13w, r15w
  xor r14w, ax
  xor r14w, bx
  xor r14w, cx
  xor r14w, dx
  xor r14w, di
  xor r14w, si
  xor r14w, bp
  xor r14w, sp
  xor r14w, r8w
  xor r14w, r9w
  xor r14w, r10w
  xor r14w, r11w
  xor r14w, r12w
  xor r14w, r13w
  xor r14w, r14w
  xor r14w, r15w
  xor r15w, ax
  xor r15w, bx
  xor r15w, cx
  xor r15w, dx
  xor r15w, di
  xor r15w, si
  xor r15w, bp
  xor r15w, sp
  xor r15w, r8w
  xor r15w, r9w
  xor r15w, r10w
  xor r15w, r11w
  xor r15w, r12w
  xor r15w, r13w
  xor r15w, r14w
  xor r15w, r15w


; xor m16,r16

  xor word [mem16], ax
  xor word [mem16], bx
  xor word [mem16], cx
  xor word [mem16], dx
  xor word [mem16], di
  xor word [mem16], si
  xor word [mem16], bp
  xor word [mem16], sp
  xor word [mem16], r8w
  xor word [mem16], r9w
  xor word [mem16], r10w
  xor word [mem16], r11w
  xor word [mem16], r12w
  xor word [mem16], r13w
  xor word [mem16], r14w
  xor word [mem16], r15w


; xor r16,m16

  xor ax, word [mem16]
  xor bx, word [mem16]
  xor cx, word [mem16]
  xor dx, word [mem16]
  xor di, word [mem16]
  xor si, word [mem16]
  xor bp, word [mem16]
  xor sp, word [mem16]
  xor r8w, word [mem16]
  xor r9w, word [mem16]
  xor r10w, word [mem16]
  xor r11w, word [mem16]
  xor r12w, word [mem16]
  xor r13w, word [mem16]
  xor r14w, word [mem16]
  xor r15w, word [mem16]


; xor r16,i16

  xor ax, imm16
  xor bx, imm16
  xor cx, imm16
  xor dx, imm16
  xor di, imm16
  xor si, imm16
  xor bp, imm16
  xor sp, imm16
  xor r8w, imm16
  xor r9w, imm16
  xor r10w, imm16
  xor r11w, imm16
  xor r12w, imm16
  xor r13w, imm16
  xor r14w, imm16
  xor r15w, imm16


; xor m16,i16

  xor word [mem16], imm16


; xor r32,r32

  xor eax, eax
  xor eax, ebx
  xor eax, ecx
  xor eax, edx
  xor eax, edi
  xor eax, esi
  xor eax, ebp
  xor eax, esp
  xor eax, r8d
  xor eax, r9d
  xor eax, r10d
  xor eax, r11d
  xor eax, r12d
  xor eax, r13d
  xor eax, r14d
  xor eax, r15d
  xor ebx, eax
  xor ebx, ebx
  xor ebx, ecx
  xor ebx, edx
  xor ebx, edi
  xor ebx, esi
  xor ebx, ebp
  xor ebx, esp
  xor ebx, r8d
  xor ebx, r9d
  xor ebx, r10d
  xor ebx, r11d
  xor ebx, r12d
  xor ebx, r13d
  xor ebx, r14d
  xor ebx, r15d
  xor ecx, eax
  xor ecx, ebx
  xor ecx, ecx
  xor ecx, edx
  xor ecx, edi
  xor ecx, esi
  xor ecx, ebp
  xor ecx, esp
  xor ecx, r8d
  xor ecx, r9d
  xor ecx, r10d
  xor ecx, r11d
  xor ecx, r12d
  xor ecx, r13d
  xor ecx, r14d
  xor ecx, r15d
  xor edx, eax
  xor edx, ebx
  xor edx, ecx
  xor edx, edx
  xor edx, edi
  xor edx, esi
  xor edx, ebp
  xor edx, esp
  xor edx, r8d
  xor edx, r9d
  xor edx, r10d
  xor edx, r11d
  xor edx, r12d
  xor edx, r13d
  xor edx, r14d
  xor edx, r15d
  xor edi, eax
  xor edi, ebx
  xor edi, ecx
  xor edi, edx
  xor edi, edi
  xor edi, esi
  xor edi, ebp
  xor edi, esp
  xor edi, r8d
  xor edi, r9d
  xor edi, r10d
  xor edi, r11d
  xor edi, r12d
  xor edi, r13d
  xor edi, r14d
  xor edi, r15d
  xor esi, eax
  xor esi, ebx
  xor esi, ecx
  xor esi, edx
  xor esi, edi
  xor esi, esi
  xor esi, ebp
  xor esi, esp
  xor esi, r8d
  xor esi, r9d
  xor esi, r10d
  xor esi, r11d
  xor esi, r12d
  xor esi, r13d
  xor esi, r14d
  xor esi, r15d
  xor ebp, eax
  xor ebp, ebx
  xor ebp, ecx
  xor ebp, edx
  xor ebp, edi
  xor ebp, esi
  xor ebp, ebp
  xor ebp, esp
  xor ebp, r8d
  xor ebp, r9d
  xor ebp, r10d
  xor ebp, r11d
  xor ebp, r12d
  xor ebp, r13d
  xor ebp, r14d
  xor ebp, r15d
  xor esp, eax
  xor esp, ebx
  xor esp, ecx
  xor esp, edx
  xor esp, edi
  xor esp, esi
  xor esp, ebp
  xor esp, esp
  xor esp, r8d
  xor esp, r9d
  xor esp, r10d
  xor esp, r11d
  xor esp, r12d
  xor esp, r13d
  xor esp, r14d
  xor esp, r15d
  xor r8d, eax
  xor r8d, ebx
  xor r8d, ecx
  xor r8d, edx
  xor r8d, edi
  xor r8d, esi
  xor r8d, ebp
  xor r8d, esp
  xor r8d, r8d
  xor r8d, r9d
  xor r8d, r10d
  xor r8d, r11d
  xor r8d, r12d
  xor r8d, r13d
  xor r8d, r14d
  xor r8d, r15d
  xor r9d, eax
  xor r9d, ebx
  xor r9d, ecx
  xor r9d, edx
  xor r9d, edi
  xor r9d, esi
  xor r9d, ebp
  xor r9d, esp
  xor r9d, r8d
  xor r9d, r9d
  xor r9d, r10d
  xor r9d, r11d
  xor r9d, r12d
  xor r9d, r13d
  xor r9d, r14d
  xor r9d, r15d
  xor r10d, eax
  xor r10d, ebx
  xor r10d, ecx
  xor r10d, edx
  xor r10d, edi
  xor r10d, esi
  xor r10d, ebp
  xor r10d, esp
  xor r10d, r8d
  xor r10d, r9d
  xor r10d, r10d
  xor r10d, r11d
  xor r10d, r12d
  xor r10d, r13d
  xor r10d, r14d
  xor r10d, r15d
  xor r11d, eax
  xor r11d, ebx
  xor r11d, ecx
  xor r11d, edx
  xor r11d, edi
  xor r11d, esi
  xor r11d, ebp
  xor r11d, esp
  xor r11d, r8d
  xor r11d, r9d
  xor r11d, r10d
  xor r11d, r11d
  xor r11d, r12d
  xor r11d, r13d
  xor r11d, r14d
  xor r11d, r15d
  xor r12d, eax
  xor r12d, ebx
  xor r12d, ecx
  xor r12d, edx
  xor r12d, edi
  xor r12d, esi
  xor r12d, ebp
  xor r12d, esp
  xor r12d, r8d
  xor r12d, r9d
  xor r12d, r10d
  xor r12d, r11d
  xor r12d, r12d
  xor r12d, r13d
  xor r12d, r14d
  xor r12d, r15d
  xor r13d, eax
  xor r13d, ebx
  xor r13d, ecx
  xor r13d, edx
  xor r13d, edi
  xor r13d, esi
  xor r13d, ebp
  xor r13d, esp
  xor r13d, r8d
  xor r13d, r9d
  xor r13d, r10d
  xor r13d, r11d
  xor r13d, r12d
  xor r13d, r13d
  xor r13d, r14d
  xor r13d, r15d
  xor r14d, eax
  xor r14d, ebx
  xor r14d, ecx
  xor r14d, edx
  xor r14d, edi
  xor r14d, esi
  xor r14d, ebp
  xor r14d, esp
  xor r14d, r8d
  xor r14d, r9d
  xor r14d, r10d
  xor r14d, r11d
  xor r14d, r12d
  xor r14d, r13d
  xor r14d, r14d
  xor r14d, r15d
  xor r15d, eax
  xor r15d, ebx
  xor r15d, ecx
  xor r15d, edx
  xor r15d, edi
  xor r15d, esi
  xor r15d, ebp
  xor r15d, esp
  xor r15d, r8d
  xor r15d, r9d
  xor r15d, r10d
  xor r15d, r11d
  xor r15d, r12d
  xor r15d, r13d
  xor r15d, r14d
  xor r15d, r15d


; xor m32,r32

  xor dword [mem32], eax
  xor dword [mem32], ebx
  xor dword [mem32], ecx
  xor dword [mem32], edx
  xor dword [mem32], edi
  xor dword [mem32], esi
  xor dword [mem32], ebp
  xor dword [mem32], esp
  xor dword [mem32], r8d
  xor dword [mem32], r9d
  xor dword [mem32], r10d
  xor dword [mem32], r11d
  xor dword [mem32], r12d
  xor dword [mem32], r13d
  xor dword [mem32], r14d
  xor dword [mem32], r15d


; xor r32,m32

  xor eax, dword [mem32]
  xor ebx, dword [mem32]
  xor ecx, dword [mem32]
  xor edx, dword [mem32]
  xor edi, dword [mem32]
  xor esi, dword [mem32]
  xor ebp, dword [mem32]
  xor esp, dword [mem32]
  xor r8d, dword [mem32]
  xor r9d, dword [mem32]
  xor r10d, dword [mem32]
  xor r11d, dword [mem32]
  xor r12d, dword [mem32]
  xor r13d, dword [mem32]
  xor r14d, dword [mem32]
  xor r15d, dword [mem32]


; xor r32,i32

  xor eax, imm32
  xor ebx, imm32
  xor ecx, imm32
  xor edx, imm32
  xor edi, imm32
  xor esi, imm32
  xor ebp, imm32
  xor esp, imm32
  xor r8d, imm32
  xor r9d, imm32
  xor r10d, imm32
  xor r11d, imm32
  xor r12d, imm32
  xor r13d, imm32
  xor r14d, imm32
  xor r15d, imm32


; xor m32,i32

  xor dword [mem32], imm32


; xor r64,r64

  xor rax, rax
  xor rax, rbx
  xor rax, rcx
  xor rax, rdx
  xor rax, rdi
  xor rax, rsi
  xor rax, rbp
  xor rax, rsp
  xor rax, r8
  xor rax, r9
  xor rax, r10
  xor rax, r11
  xor rax, r12
  xor rax, r13
  xor rax, r14
  xor rax, r15
  xor rbx, rax
  xor rbx, rbx
  xor rbx, rcx
  xor rbx, rdx
  xor rbx, rdi
  xor rbx, rsi
  xor rbx, rbp
  xor rbx, rsp
  xor rbx, r8
  xor rbx, r9
  xor rbx, r10
  xor rbx, r11
  xor rbx, r12
  xor rbx, r13
  xor rbx, r14
  xor rbx, r15
  xor rcx, rax
  xor rcx, rbx
  xor rcx, rcx
  xor rcx, rdx
  xor rcx, rdi
  xor rcx, rsi
  xor rcx, rbp
  xor rcx, rsp
  xor rcx, r8
  xor rcx, r9
  xor rcx, r10
  xor rcx, r11
  xor rcx, r12
  xor rcx, r13
  xor rcx, r14
  xor rcx, r15
  xor rdx, rax
  xor rdx, rbx
  xor rdx, rcx
  xor rdx, rdx
  xor rdx, rdi
  xor rdx, rsi
  xor rdx, rbp
  xor rdx, rsp
  xor rdx, r8
  xor rdx, r9
  xor rdx, r10
  xor rdx, r11
  xor rdx, r12
  xor rdx, r13
  xor rdx, r14
  xor rdx, r15
  xor rdi, rax
  xor rdi, rbx
  xor rdi, rcx
  xor rdi, rdx
  xor rdi, rdi
  xor rdi, rsi
  xor rdi, rbp
  xor rdi, rsp
  xor rdi, r8
  xor rdi, r9
  xor rdi, r10
  xor rdi, r11
  xor rdi, r12
  xor rdi, r13
  xor rdi, r14
  xor rdi, r15
  xor rsi, rax
  xor rsi, rbx
  xor rsi, rcx
  xor rsi, rdx
  xor rsi, rdi
  xor rsi, rsi
  xor rsi, rbp
  xor rsi, rsp
  xor rsi, r8
  xor rsi, r9
  xor rsi, r10
  xor rsi, r11
  xor rsi, r12
  xor rsi, r13
  xor rsi, r14
  xor rsi, r15
  xor rbp, rax
  xor rbp, rbx
  xor rbp, rcx
  xor rbp, rdx
  xor rbp, rdi
  xor rbp, rsi
  xor rbp, rbp
  xor rbp, rsp
  xor rbp, r8
  xor rbp, r9
  xor rbp, r10
  xor rbp, r11
  xor rbp, r12
  xor rbp, r13
  xor rbp, r14
  xor rbp, r15
  xor rsp, rax
  xor rsp, rbx
  xor rsp, rcx
  xor rsp, rdx
  xor rsp, rdi
  xor rsp, rsi
  xor rsp, rbp
  xor rsp, rsp
  xor rsp, r8
  xor rsp, r9
  xor rsp, r10
  xor rsp, r11
  xor rsp, r12
  xor rsp, r13
  xor rsp, r14
  xor rsp, r15
  xor r8, rax
  xor r8, rbx
  xor r8, rcx
  xor r8, rdx
  xor r8, rdi
  xor r8, rsi
  xor r8, rbp
  xor r8, rsp
  xor r8, r8
  xor r8, r9
  xor r8, r10
  xor r8, r11
  xor r8, r12
  xor r8, r13
  xor r8, r14
  xor r8, r15
  xor r9, rax
  xor r9, rbx
  xor r9, rcx
  xor r9, rdx
  xor r9, rdi
  xor r9, rsi
  xor r9, rbp
  xor r9, rsp
  xor r9, r8
  xor r9, r9
  xor r9, r10
  xor r9, r11
  xor r9, r12
  xor r9, r13
  xor r9, r14
  xor r9, r15
  xor r10, rax
  xor r10, rbx
  xor r10, rcx
  xor r10, rdx
  xor r10, rdi
  xor r10, rsi
  xor r10, rbp
  xor r10, rsp
  xor r10, r8
  xor r10, r9
  xor r10, r10
  xor r10, r11
  xor r10, r12
  xor r10, r13
  xor r10, r14
  xor r10, r15
  xor r11, rax
  xor r11, rbx
  xor r11, rcx
  xor r11, rdx
  xor r11, rdi
  xor r11, rsi
  xor r11, rbp
  xor r11, rsp
  xor r11, r8
  xor r11, r9
  xor r11, r10
  xor r11, r11
  xor r11, r12
  xor r11, r13
  xor r11, r14
  xor r11, r15
  xor r12, rax
  xor r12, rbx
  xor r12, rcx
  xor r12, rdx
  xor r12, rdi
  xor r12, rsi
  xor r12, rbp
  xor r12, rsp
  xor r12, r8
  xor r12, r9
  xor r12, r10
  xor r12, r11
  xor r12, r12
  xor r12, r13
  xor r12, r14
  xor r12, r15
  xor r13, rax
  xor r13, rbx
  xor r13, rcx
  xor r13, rdx
  xor r13, rdi
  xor r13, rsi
  xor r13, rbp
  xor r13, rsp
  xor r13, r8
  xor r13, r9
  xor r13, r10
  xor r13, r11
  xor r13, r12
  xor r13, r13
  xor r13, r14
  xor r13, r15
  xor r14, rax
  xor r14, rbx
  xor r14, rcx
  xor r14, rdx
  xor r14, rdi
  xor r14, rsi
  xor r14, rbp
  xor r14, rsp
  xor r14, r8
  xor r14, r9
  xor r14, r10
  xor r14, r11
  xor r14, r12
  xor r14, r13
  xor r14, r14
  xor r14, r15
  xor r15, rax
  xor r15, rbx
  xor r15, rcx
  xor r15, rdx
  xor r15, rdi
  xor r15, rsi
  xor r15, rbp
  xor r15, rsp
  xor r15, r8
  xor r15, r9
  xor r15, r10
  xor r15, r11
  xor r15, r12
  xor r15, r13
  xor r15, r14
  xor r15, r15


; xor m64,r64

  xor qword [mem64], rax
  xor qword [mem64], rbx
  xor qword [mem64], rcx
  xor qword [mem64], rdx
  xor qword [mem64], rdi
  xor qword [mem64], rsi
  xor qword [mem64], rbp
  xor qword [mem64], rsp
  xor qword [mem64], r8
  xor qword [mem64], r9
  xor qword [mem64], r10
  xor qword [mem64], r11
  xor qword [mem64], r12
  xor qword [mem64], r13
  xor qword [mem64], r14
  xor qword [mem64], r15


; xor r64,m64

  xor rax, qword [mem64]
  xor rbx, qword [mem64]
  xor rcx, qword [mem64]
  xor rdx, qword [mem64]
  xor rdi, qword [mem64]
  xor rsi, qword [mem64]
  xor rbp, qword [mem64]
  xor rsp, qword [mem64]
  xor r8, qword [mem64]
  xor r9, qword [mem64]
  xor r10, qword [mem64]
  xor r11, qword [mem64]
  xor r12, qword [mem64]
  xor r13, qword [mem64]
  xor r14, qword [mem64]
  xor r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
