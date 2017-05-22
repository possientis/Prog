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

; and r8,r8

  and al, al
  and al, bl
  and al, cl
  and al, dl
  and al, dil
  and al, sil
  and al, bpl
  and al, spl
  and al, r8b
  and al, r9b
  and al, r10b
  and al, r11b
  and al, r12b
  and al, r13b
  and al, r14b
  and al, r15b
  and bl, al
  and bl, bl
  and bl, cl
  and bl, dl
  and bl, dil
  and bl, sil
  and bl, bpl
  and bl, spl
  and bl, r8b
  and bl, r9b
  and bl, r10b
  and bl, r11b
  and bl, r12b
  and bl, r13b
  and bl, r14b
  and bl, r15b
  and cl, al
  and cl, bl
  and cl, cl
  and cl, dl
  and cl, dil
  and cl, sil
  and cl, bpl
  and cl, spl
  and cl, r8b
  and cl, r9b
  and cl, r10b
  and cl, r11b
  and cl, r12b
  and cl, r13b
  and cl, r14b
  and cl, r15b
  and dl, al
  and dl, bl
  and dl, cl
  and dl, dl
  and dl, dil
  and dl, sil
  and dl, bpl
  and dl, spl
  and dl, r8b
  and dl, r9b
  and dl, r10b
  and dl, r11b
  and dl, r12b
  and dl, r13b
  and dl, r14b
  and dl, r15b
  and dil, al
  and dil, bl
  and dil, cl
  and dil, dl
  and dil, dil
  and dil, sil
  and dil, bpl
  and dil, spl
  and dil, r8b
  and dil, r9b
  and dil, r10b
  and dil, r11b
  and dil, r12b
  and dil, r13b
  and dil, r14b
  and dil, r15b
  and sil, al
  and sil, bl
  and sil, cl
  and sil, dl
  and sil, dil
  and sil, sil
  and sil, bpl
  and sil, spl
  and sil, r8b
  and sil, r9b
  and sil, r10b
  and sil, r11b
  and sil, r12b
  and sil, r13b
  and sil, r14b
  and sil, r15b
  and bpl, al
  and bpl, bl
  and bpl, cl
  and bpl, dl
  and bpl, dil
  and bpl, sil
  and bpl, bpl
  and bpl, spl
  and bpl, r8b
  and bpl, r9b
  and bpl, r10b
  and bpl, r11b
  and bpl, r12b
  and bpl, r13b
  and bpl, r14b
  and bpl, r15b
  and spl, al
  and spl, bl
  and spl, cl
  and spl, dl
  and spl, dil
  and spl, sil
  and spl, bpl
  and spl, spl
  and spl, r8b
  and spl, r9b
  and spl, r10b
  and spl, r11b
  and spl, r12b
  and spl, r13b
  and spl, r14b
  and spl, r15b
  and r8b, al
  and r8b, bl
  and r8b, cl
  and r8b, dl
  and r8b, dil
  and r8b, sil
  and r8b, bpl
  and r8b, spl
  and r8b, r8b
  and r8b, r9b
  and r8b, r10b
  and r8b, r11b
  and r8b, r12b
  and r8b, r13b
  and r8b, r14b
  and r8b, r15b
  and r9b, al
  and r9b, bl
  and r9b, cl
  and r9b, dl
  and r9b, dil
  and r9b, sil
  and r9b, bpl
  and r9b, spl
  and r9b, r8b
  and r9b, r9b
  and r9b, r10b
  and r9b, r11b
  and r9b, r12b
  and r9b, r13b
  and r9b, r14b
  and r9b, r15b
  and r10b, al
  and r10b, bl
  and r10b, cl
  and r10b, dl
  and r10b, dil
  and r10b, sil
  and r10b, bpl
  and r10b, spl
  and r10b, r8b
  and r10b, r9b
  and r10b, r10b
  and r10b, r11b
  and r10b, r12b
  and r10b, r13b
  and r10b, r14b
  and r10b, r15b
  and r11b, al
  and r11b, bl
  and r11b, cl
  and r11b, dl
  and r11b, dil
  and r11b, sil
  and r11b, bpl
  and r11b, spl
  and r11b, r8b
  and r11b, r9b
  and r11b, r10b
  and r11b, r11b
  and r11b, r12b
  and r11b, r13b
  and r11b, r14b
  and r11b, r15b
  and r12b, al
  and r12b, bl
  and r12b, cl
  and r12b, dl
  and r12b, dil
  and r12b, sil
  and r12b, bpl
  and r12b, spl
  and r12b, r8b
  and r12b, r9b
  and r12b, r10b
  and r12b, r11b
  and r12b, r12b
  and r12b, r13b
  and r12b, r14b
  and r12b, r15b
  and r13b, al
  and r13b, bl
  and r13b, cl
  and r13b, dl
  and r13b, dil
  and r13b, sil
  and r13b, bpl
  and r13b, spl
  and r13b, r8b
  and r13b, r9b
  and r13b, r10b
  and r13b, r11b
  and r13b, r12b
  and r13b, r13b
  and r13b, r14b
  and r13b, r15b
  and r14b, al
  and r14b, bl
  and r14b, cl
  and r14b, dl
  and r14b, dil
  and r14b, sil
  and r14b, bpl
  and r14b, spl
  and r14b, r8b
  and r14b, r9b
  and r14b, r10b
  and r14b, r11b
  and r14b, r12b
  and r14b, r13b
  and r14b, r14b
  and r14b, r15b
  and r15b, al
  and r15b, bl
  and r15b, cl
  and r15b, dl
  and r15b, dil
  and r15b, sil
  and r15b, bpl
  and r15b, spl
  and r15b, r8b
  and r15b, r9b
  and r15b, r10b
  and r15b, r11b
  and r15b, r12b
  and r15b, r13b
  and r15b, r14b
  and r15b, r15b


; and m8,r8

  and byte [mem8], al
  and byte [mem8], bl
  and byte [mem8], cl
  and byte [mem8], dl
  and byte [mem8], dil
  and byte [mem8], sil
  and byte [mem8], bpl
  and byte [mem8], spl
  and byte [mem8], r8b
  and byte [mem8], r9b
  and byte [mem8], r10b
  and byte [mem8], r11b
  and byte [mem8], r12b
  and byte [mem8], r13b
  and byte [mem8], r14b
  and byte [mem8], r15b


; and r8,m8

  and al, byte [mem8]
  and bl, byte [mem8]
  and cl, byte [mem8]
  and dl, byte [mem8]
  and dil, byte [mem8]
  and sil, byte [mem8]
  and bpl, byte [mem8]
  and spl, byte [mem8]
  and r8b, byte [mem8]
  and r9b, byte [mem8]
  and r10b, byte [mem8]
  and r11b, byte [mem8]
  and r12b, byte [mem8]
  and r13b, byte [mem8]
  and r14b, byte [mem8]
  and r15b, byte [mem8]


; and r8,i8

  and al, imm8
  and bl, imm8
  and cl, imm8
  and dl, imm8
  and dil, imm8
  and sil, imm8
  and bpl, imm8
  and spl, imm8
  and r8b, imm8
  and r9b, imm8
  and r10b, imm8
  and r11b, imm8
  and r12b, imm8
  and r13b, imm8
  and r14b, imm8
  and r15b, imm8


; and m8,i8

  and byte [mem8], imm8


; and r16,r16

  and ax, ax
  and ax, bx
  and ax, cx
  and ax, dx
  and ax, di
  and ax, si
  and ax, bp
  and ax, sp
  and ax, r8w
  and ax, r9w
  and ax, r10w
  and ax, r11w
  and ax, r12w
  and ax, r13w
  and ax, r14w
  and ax, r15w
  and bx, ax
  and bx, bx
  and bx, cx
  and bx, dx
  and bx, di
  and bx, si
  and bx, bp
  and bx, sp
  and bx, r8w
  and bx, r9w
  and bx, r10w
  and bx, r11w
  and bx, r12w
  and bx, r13w
  and bx, r14w
  and bx, r15w
  and cx, ax
  and cx, bx
  and cx, cx
  and cx, dx
  and cx, di
  and cx, si
  and cx, bp
  and cx, sp
  and cx, r8w
  and cx, r9w
  and cx, r10w
  and cx, r11w
  and cx, r12w
  and cx, r13w
  and cx, r14w
  and cx, r15w
  and dx, ax
  and dx, bx
  and dx, cx
  and dx, dx
  and dx, di
  and dx, si
  and dx, bp
  and dx, sp
  and dx, r8w
  and dx, r9w
  and dx, r10w
  and dx, r11w
  and dx, r12w
  and dx, r13w
  and dx, r14w
  and dx, r15w
  and di, ax
  and di, bx
  and di, cx
  and di, dx
  and di, di
  and di, si
  and di, bp
  and di, sp
  and di, r8w
  and di, r9w
  and di, r10w
  and di, r11w
  and di, r12w
  and di, r13w
  and di, r14w
  and di, r15w
  and si, ax
  and si, bx
  and si, cx
  and si, dx
  and si, di
  and si, si
  and si, bp
  and si, sp
  and si, r8w
  and si, r9w
  and si, r10w
  and si, r11w
  and si, r12w
  and si, r13w
  and si, r14w
  and si, r15w
  and bp, ax
  and bp, bx
  and bp, cx
  and bp, dx
  and bp, di
  and bp, si
  and bp, bp
  and bp, sp
  and bp, r8w
  and bp, r9w
  and bp, r10w
  and bp, r11w
  and bp, r12w
  and bp, r13w
  and bp, r14w
  and bp, r15w
  and sp, ax
  and sp, bx
  and sp, cx
  and sp, dx
  and sp, di
  and sp, si
  and sp, bp
  and sp, sp
  and sp, r8w
  and sp, r9w
  and sp, r10w
  and sp, r11w
  and sp, r12w
  and sp, r13w
  and sp, r14w
  and sp, r15w
  and r8w, ax
  and r8w, bx
  and r8w, cx
  and r8w, dx
  and r8w, di
  and r8w, si
  and r8w, bp
  and r8w, sp
  and r8w, r8w
  and r8w, r9w
  and r8w, r10w
  and r8w, r11w
  and r8w, r12w
  and r8w, r13w
  and r8w, r14w
  and r8w, r15w
  and r9w, ax
  and r9w, bx
  and r9w, cx
  and r9w, dx
  and r9w, di
  and r9w, si
  and r9w, bp
  and r9w, sp
  and r9w, r8w
  and r9w, r9w
  and r9w, r10w
  and r9w, r11w
  and r9w, r12w
  and r9w, r13w
  and r9w, r14w
  and r9w, r15w
  and r10w, ax
  and r10w, bx
  and r10w, cx
  and r10w, dx
  and r10w, di
  and r10w, si
  and r10w, bp
  and r10w, sp
  and r10w, r8w
  and r10w, r9w
  and r10w, r10w
  and r10w, r11w
  and r10w, r12w
  and r10w, r13w
  and r10w, r14w
  and r10w, r15w
  and r11w, ax
  and r11w, bx
  and r11w, cx
  and r11w, dx
  and r11w, di
  and r11w, si
  and r11w, bp
  and r11w, sp
  and r11w, r8w
  and r11w, r9w
  and r11w, r10w
  and r11w, r11w
  and r11w, r12w
  and r11w, r13w
  and r11w, r14w
  and r11w, r15w
  and r12w, ax
  and r12w, bx
  and r12w, cx
  and r12w, dx
  and r12w, di
  and r12w, si
  and r12w, bp
  and r12w, sp
  and r12w, r8w
  and r12w, r9w
  and r12w, r10w
  and r12w, r11w
  and r12w, r12w
  and r12w, r13w
  and r12w, r14w
  and r12w, r15w
  and r13w, ax
  and r13w, bx
  and r13w, cx
  and r13w, dx
  and r13w, di
  and r13w, si
  and r13w, bp
  and r13w, sp
  and r13w, r8w
  and r13w, r9w
  and r13w, r10w
  and r13w, r11w
  and r13w, r12w
  and r13w, r13w
  and r13w, r14w
  and r13w, r15w
  and r14w, ax
  and r14w, bx
  and r14w, cx
  and r14w, dx
  and r14w, di
  and r14w, si
  and r14w, bp
  and r14w, sp
  and r14w, r8w
  and r14w, r9w
  and r14w, r10w
  and r14w, r11w
  and r14w, r12w
  and r14w, r13w
  and r14w, r14w
  and r14w, r15w
  and r15w, ax
  and r15w, bx
  and r15w, cx
  and r15w, dx
  and r15w, di
  and r15w, si
  and r15w, bp
  and r15w, sp
  and r15w, r8w
  and r15w, r9w
  and r15w, r10w
  and r15w, r11w
  and r15w, r12w
  and r15w, r13w
  and r15w, r14w
  and r15w, r15w


; and m16,r16

  and word [mem16], ax
  and word [mem16], bx
  and word [mem16], cx
  and word [mem16], dx
  and word [mem16], di
  and word [mem16], si
  and word [mem16], bp
  and word [mem16], sp
  and word [mem16], r8w
  and word [mem16], r9w
  and word [mem16], r10w
  and word [mem16], r11w
  and word [mem16], r12w
  and word [mem16], r13w
  and word [mem16], r14w
  and word [mem16], r15w


; and r16,m16

  and ax, word [mem16]
  and bx, word [mem16]
  and cx, word [mem16]
  and dx, word [mem16]
  and di, word [mem16]
  and si, word [mem16]
  and bp, word [mem16]
  and sp, word [mem16]
  and r8w, word [mem16]
  and r9w, word [mem16]
  and r10w, word [mem16]
  and r11w, word [mem16]
  and r12w, word [mem16]
  and r13w, word [mem16]
  and r14w, word [mem16]
  and r15w, word [mem16]


; and r16,i16

  and ax, imm16
  and bx, imm16
  and cx, imm16
  and dx, imm16
  and di, imm16
  and si, imm16
  and bp, imm16
  and sp, imm16
  and r8w, imm16
  and r9w, imm16
  and r10w, imm16
  and r11w, imm16
  and r12w, imm16
  and r13w, imm16
  and r14w, imm16
  and r15w, imm16


; and m16,i16

  and word [mem16], imm16


; and r32,r32

  and eax, eax
  and eax, ebx
  and eax, ecx
  and eax, edx
  and eax, edi
  and eax, esi
  and eax, ebp
  and eax, esp
  and eax, r8d
  and eax, r9d
  and eax, r10d
  and eax, r11d
  and eax, r12d
  and eax, r13d
  and eax, r14d
  and eax, r15d
  and ebx, eax
  and ebx, ebx
  and ebx, ecx
  and ebx, edx
  and ebx, edi
  and ebx, esi
  and ebx, ebp
  and ebx, esp
  and ebx, r8d
  and ebx, r9d
  and ebx, r10d
  and ebx, r11d
  and ebx, r12d
  and ebx, r13d
  and ebx, r14d
  and ebx, r15d
  and ecx, eax
  and ecx, ebx
  and ecx, ecx
  and ecx, edx
  and ecx, edi
  and ecx, esi
  and ecx, ebp
  and ecx, esp
  and ecx, r8d
  and ecx, r9d
  and ecx, r10d
  and ecx, r11d
  and ecx, r12d
  and ecx, r13d
  and ecx, r14d
  and ecx, r15d
  and edx, eax
  and edx, ebx
  and edx, ecx
  and edx, edx
  and edx, edi
  and edx, esi
  and edx, ebp
  and edx, esp
  and edx, r8d
  and edx, r9d
  and edx, r10d
  and edx, r11d
  and edx, r12d
  and edx, r13d
  and edx, r14d
  and edx, r15d
  and edi, eax
  and edi, ebx
  and edi, ecx
  and edi, edx
  and edi, edi
  and edi, esi
  and edi, ebp
  and edi, esp
  and edi, r8d
  and edi, r9d
  and edi, r10d
  and edi, r11d
  and edi, r12d
  and edi, r13d
  and edi, r14d
  and edi, r15d
  and esi, eax
  and esi, ebx
  and esi, ecx
  and esi, edx
  and esi, edi
  and esi, esi
  and esi, ebp
  and esi, esp
  and esi, r8d
  and esi, r9d
  and esi, r10d
  and esi, r11d
  and esi, r12d
  and esi, r13d
  and esi, r14d
  and esi, r15d
  and ebp, eax
  and ebp, ebx
  and ebp, ecx
  and ebp, edx
  and ebp, edi
  and ebp, esi
  and ebp, ebp
  and ebp, esp
  and ebp, r8d
  and ebp, r9d
  and ebp, r10d
  and ebp, r11d
  and ebp, r12d
  and ebp, r13d
  and ebp, r14d
  and ebp, r15d
  and esp, eax
  and esp, ebx
  and esp, ecx
  and esp, edx
  and esp, edi
  and esp, esi
  and esp, ebp
  and esp, esp
  and esp, r8d
  and esp, r9d
  and esp, r10d
  and esp, r11d
  and esp, r12d
  and esp, r13d
  and esp, r14d
  and esp, r15d
  and r8d, eax
  and r8d, ebx
  and r8d, ecx
  and r8d, edx
  and r8d, edi
  and r8d, esi
  and r8d, ebp
  and r8d, esp
  and r8d, r8d
  and r8d, r9d
  and r8d, r10d
  and r8d, r11d
  and r8d, r12d
  and r8d, r13d
  and r8d, r14d
  and r8d, r15d
  and r9d, eax
  and r9d, ebx
  and r9d, ecx
  and r9d, edx
  and r9d, edi
  and r9d, esi
  and r9d, ebp
  and r9d, esp
  and r9d, r8d
  and r9d, r9d
  and r9d, r10d
  and r9d, r11d
  and r9d, r12d
  and r9d, r13d
  and r9d, r14d
  and r9d, r15d
  and r10d, eax
  and r10d, ebx
  and r10d, ecx
  and r10d, edx
  and r10d, edi
  and r10d, esi
  and r10d, ebp
  and r10d, esp
  and r10d, r8d
  and r10d, r9d
  and r10d, r10d
  and r10d, r11d
  and r10d, r12d
  and r10d, r13d
  and r10d, r14d
  and r10d, r15d
  and r11d, eax
  and r11d, ebx
  and r11d, ecx
  and r11d, edx
  and r11d, edi
  and r11d, esi
  and r11d, ebp
  and r11d, esp
  and r11d, r8d
  and r11d, r9d
  and r11d, r10d
  and r11d, r11d
  and r11d, r12d
  and r11d, r13d
  and r11d, r14d
  and r11d, r15d
  and r12d, eax
  and r12d, ebx
  and r12d, ecx
  and r12d, edx
  and r12d, edi
  and r12d, esi
  and r12d, ebp
  and r12d, esp
  and r12d, r8d
  and r12d, r9d
  and r12d, r10d
  and r12d, r11d
  and r12d, r12d
  and r12d, r13d
  and r12d, r14d
  and r12d, r15d
  and r13d, eax
  and r13d, ebx
  and r13d, ecx
  and r13d, edx
  and r13d, edi
  and r13d, esi
  and r13d, ebp
  and r13d, esp
  and r13d, r8d
  and r13d, r9d
  and r13d, r10d
  and r13d, r11d
  and r13d, r12d
  and r13d, r13d
  and r13d, r14d
  and r13d, r15d
  and r14d, eax
  and r14d, ebx
  and r14d, ecx
  and r14d, edx
  and r14d, edi
  and r14d, esi
  and r14d, ebp
  and r14d, esp
  and r14d, r8d
  and r14d, r9d
  and r14d, r10d
  and r14d, r11d
  and r14d, r12d
  and r14d, r13d
  and r14d, r14d
  and r14d, r15d
  and r15d, eax
  and r15d, ebx
  and r15d, ecx
  and r15d, edx
  and r15d, edi
  and r15d, esi
  and r15d, ebp
  and r15d, esp
  and r15d, r8d
  and r15d, r9d
  and r15d, r10d
  and r15d, r11d
  and r15d, r12d
  and r15d, r13d
  and r15d, r14d
  and r15d, r15d


; and m32,r32

  and dword [mem32], eax
  and dword [mem32], ebx
  and dword [mem32], ecx
  and dword [mem32], edx
  and dword [mem32], edi
  and dword [mem32], esi
  and dword [mem32], ebp
  and dword [mem32], esp
  and dword [mem32], r8d
  and dword [mem32], r9d
  and dword [mem32], r10d
  and dword [mem32], r11d
  and dword [mem32], r12d
  and dword [mem32], r13d
  and dword [mem32], r14d
  and dword [mem32], r15d


; and r32,m32

  and eax, dword [mem32]
  and ebx, dword [mem32]
  and ecx, dword [mem32]
  and edx, dword [mem32]
  and edi, dword [mem32]
  and esi, dword [mem32]
  and ebp, dword [mem32]
  and esp, dword [mem32]
  and r8d, dword [mem32]
  and r9d, dword [mem32]
  and r10d, dword [mem32]
  and r11d, dword [mem32]
  and r12d, dword [mem32]
  and r13d, dword [mem32]
  and r14d, dword [mem32]
  and r15d, dword [mem32]


; and r32,i32

  and eax, imm32
  and ebx, imm32
  and ecx, imm32
  and edx, imm32
  and edi, imm32
  and esi, imm32
  and ebp, imm32
  and esp, imm32
  and r8d, imm32
  and r9d, imm32
  and r10d, imm32
  and r11d, imm32
  and r12d, imm32
  and r13d, imm32
  and r14d, imm32
  and r15d, imm32


; and m32,i32

  and dword [mem32], imm32


; and r64,r64

  and rax, rax
  and rax, rbx
  and rax, rcx
  and rax, rdx
  and rax, rdi
  and rax, rsi
  and rax, rbp
  and rax, rsp
  and rax, r8
  and rax, r9
  and rax, r10
  and rax, r11
  and rax, r12
  and rax, r13
  and rax, r14
  and rax, r15
  and rbx, rax
  and rbx, rbx
  and rbx, rcx
  and rbx, rdx
  and rbx, rdi
  and rbx, rsi
  and rbx, rbp
  and rbx, rsp
  and rbx, r8
  and rbx, r9
  and rbx, r10
  and rbx, r11
  and rbx, r12
  and rbx, r13
  and rbx, r14
  and rbx, r15
  and rcx, rax
  and rcx, rbx
  and rcx, rcx
  and rcx, rdx
  and rcx, rdi
  and rcx, rsi
  and rcx, rbp
  and rcx, rsp
  and rcx, r8
  and rcx, r9
  and rcx, r10
  and rcx, r11
  and rcx, r12
  and rcx, r13
  and rcx, r14
  and rcx, r15
  and rdx, rax
  and rdx, rbx
  and rdx, rcx
  and rdx, rdx
  and rdx, rdi
  and rdx, rsi
  and rdx, rbp
  and rdx, rsp
  and rdx, r8
  and rdx, r9
  and rdx, r10
  and rdx, r11
  and rdx, r12
  and rdx, r13
  and rdx, r14
  and rdx, r15
  and rdi, rax
  and rdi, rbx
  and rdi, rcx
  and rdi, rdx
  and rdi, rdi
  and rdi, rsi
  and rdi, rbp
  and rdi, rsp
  and rdi, r8
  and rdi, r9
  and rdi, r10
  and rdi, r11
  and rdi, r12
  and rdi, r13
  and rdi, r14
  and rdi, r15
  and rsi, rax
  and rsi, rbx
  and rsi, rcx
  and rsi, rdx
  and rsi, rdi
  and rsi, rsi
  and rsi, rbp
  and rsi, rsp
  and rsi, r8
  and rsi, r9
  and rsi, r10
  and rsi, r11
  and rsi, r12
  and rsi, r13
  and rsi, r14
  and rsi, r15
  and rbp, rax
  and rbp, rbx
  and rbp, rcx
  and rbp, rdx
  and rbp, rdi
  and rbp, rsi
  and rbp, rbp
  and rbp, rsp
  and rbp, r8
  and rbp, r9
  and rbp, r10
  and rbp, r11
  and rbp, r12
  and rbp, r13
  and rbp, r14
  and rbp, r15
  and rsp, rax
  and rsp, rbx
  and rsp, rcx
  and rsp, rdx
  and rsp, rdi
  and rsp, rsi
  and rsp, rbp
  and rsp, rsp
  and rsp, r8
  and rsp, r9
  and rsp, r10
  and rsp, r11
  and rsp, r12
  and rsp, r13
  and rsp, r14
  and rsp, r15
  and r8, rax
  and r8, rbx
  and r8, rcx
  and r8, rdx
  and r8, rdi
  and r8, rsi
  and r8, rbp
  and r8, rsp
  and r8, r8
  and r8, r9
  and r8, r10
  and r8, r11
  and r8, r12
  and r8, r13
  and r8, r14
  and r8, r15
  and r9, rax
  and r9, rbx
  and r9, rcx
  and r9, rdx
  and r9, rdi
  and r9, rsi
  and r9, rbp
  and r9, rsp
  and r9, r8
  and r9, r9
  and r9, r10
  and r9, r11
  and r9, r12
  and r9, r13
  and r9, r14
  and r9, r15
  and r10, rax
  and r10, rbx
  and r10, rcx
  and r10, rdx
  and r10, rdi
  and r10, rsi
  and r10, rbp
  and r10, rsp
  and r10, r8
  and r10, r9
  and r10, r10
  and r10, r11
  and r10, r12
  and r10, r13
  and r10, r14
  and r10, r15
  and r11, rax
  and r11, rbx
  and r11, rcx
  and r11, rdx
  and r11, rdi
  and r11, rsi
  and r11, rbp
  and r11, rsp
  and r11, r8
  and r11, r9
  and r11, r10
  and r11, r11
  and r11, r12
  and r11, r13
  and r11, r14
  and r11, r15
  and r12, rax
  and r12, rbx
  and r12, rcx
  and r12, rdx
  and r12, rdi
  and r12, rsi
  and r12, rbp
  and r12, rsp
  and r12, r8
  and r12, r9
  and r12, r10
  and r12, r11
  and r12, r12
  and r12, r13
  and r12, r14
  and r12, r15
  and r13, rax
  and r13, rbx
  and r13, rcx
  and r13, rdx
  and r13, rdi
  and r13, rsi
  and r13, rbp
  and r13, rsp
  and r13, r8
  and r13, r9
  and r13, r10
  and r13, r11
  and r13, r12
  and r13, r13
  and r13, r14
  and r13, r15
  and r14, rax
  and r14, rbx
  and r14, rcx
  and r14, rdx
  and r14, rdi
  and r14, rsi
  and r14, rbp
  and r14, rsp
  and r14, r8
  and r14, r9
  and r14, r10
  and r14, r11
  and r14, r12
  and r14, r13
  and r14, r14
  and r14, r15
  and r15, rax
  and r15, rbx
  and r15, rcx
  and r15, rdx
  and r15, rdi
  and r15, rsi
  and r15, rbp
  and r15, rsp
  and r15, r8
  and r15, r9
  and r15, r10
  and r15, r11
  and r15, r12
  and r15, r13
  and r15, r14
  and r15, r15


; and m64,r64

  and qword [mem64], rax
  and qword [mem64], rbx
  and qword [mem64], rcx
  and qword [mem64], rdx
  and qword [mem64], rdi
  and qword [mem64], rsi
  and qword [mem64], rbp
  and qword [mem64], rsp
  and qword [mem64], r8
  and qword [mem64], r9
  and qword [mem64], r10
  and qword [mem64], r11
  and qword [mem64], r12
  and qword [mem64], r13
  and qword [mem64], r14
  and qword [mem64], r15


; and r64,m64

  and rax, qword [mem64]
  and rbx, qword [mem64]
  and rcx, qword [mem64]
  and rdx, qword [mem64]
  and rdi, qword [mem64]
  and rsi, qword [mem64]
  and rbp, qword [mem64]
  and rsp, qword [mem64]
  and r8, qword [mem64]
  and r9, qword [mem64]
  and r10, qword [mem64]
  and r11, qword [mem64]
  and r12, qword [mem64]
  and r13, qword [mem64]
  and r14, qword [mem64]
  and r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
