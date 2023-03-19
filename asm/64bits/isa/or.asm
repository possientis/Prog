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

; or r8,r8

  or al, al
  or al, bl
  or al, cl
  or al, dl
  or al, dil
  or al, sil
  or al, bpl
  or al, spl
  or al, r8b
  or al, r9b
  or al, r10b
  or al, r11b
  or al, r12b
  or al, r13b
  or al, r14b
  or al, r15b
  or bl, al
  or bl, bl
  or bl, cl
  or bl, dl
  or bl, dil
  or bl, sil
  or bl, bpl
  or bl, spl
  or bl, r8b
  or bl, r9b
  or bl, r10b
  or bl, r11b
  or bl, r12b
  or bl, r13b
  or bl, r14b
  or bl, r15b
  or cl, al
  or cl, bl
  or cl, cl
  or cl, dl
  or cl, dil
  or cl, sil
  or cl, bpl
  or cl, spl
  or cl, r8b
  or cl, r9b
  or cl, r10b
  or cl, r11b
  or cl, r12b
  or cl, r13b
  or cl, r14b
  or cl, r15b
  or dl, al
  or dl, bl
  or dl, cl
  or dl, dl
  or dl, dil
  or dl, sil
  or dl, bpl
  or dl, spl
  or dl, r8b
  or dl, r9b
  or dl, r10b
  or dl, r11b
  or dl, r12b
  or dl, r13b
  or dl, r14b
  or dl, r15b
  or dil, al
  or dil, bl
  or dil, cl
  or dil, dl
  or dil, dil
  or dil, sil
  or dil, bpl
  or dil, spl
  or dil, r8b
  or dil, r9b
  or dil, r10b
  or dil, r11b
  or dil, r12b
  or dil, r13b
  or dil, r14b
  or dil, r15b
  or sil, al
  or sil, bl
  or sil, cl
  or sil, dl
  or sil, dil
  or sil, sil
  or sil, bpl
  or sil, spl
  or sil, r8b
  or sil, r9b
  or sil, r10b
  or sil, r11b
  or sil, r12b
  or sil, r13b
  or sil, r14b
  or sil, r15b
  or bpl, al
  or bpl, bl
  or bpl, cl
  or bpl, dl
  or bpl, dil
  or bpl, sil
  or bpl, bpl
  or bpl, spl
  or bpl, r8b
  or bpl, r9b
  or bpl, r10b
  or bpl, r11b
  or bpl, r12b
  or bpl, r13b
  or bpl, r14b
  or bpl, r15b
  or spl, al
  or spl, bl
  or spl, cl
  or spl, dl
  or spl, dil
  or spl, sil
  or spl, bpl
  or spl, spl
  or spl, r8b
  or spl, r9b
  or spl, r10b
  or spl, r11b
  or spl, r12b
  or spl, r13b
  or spl, r14b
  or spl, r15b
  or r8b, al
  or r8b, bl
  or r8b, cl
  or r8b, dl
  or r8b, dil
  or r8b, sil
  or r8b, bpl
  or r8b, spl
  or r8b, r8b
  or r8b, r9b
  or r8b, r10b
  or r8b, r11b
  or r8b, r12b
  or r8b, r13b
  or r8b, r14b
  or r8b, r15b
  or r9b, al
  or r9b, bl
  or r9b, cl
  or r9b, dl
  or r9b, dil
  or r9b, sil
  or r9b, bpl
  or r9b, spl
  or r9b, r8b
  or r9b, r9b
  or r9b, r10b
  or r9b, r11b
  or r9b, r12b
  or r9b, r13b
  or r9b, r14b
  or r9b, r15b
  or r10b, al
  or r10b, bl
  or r10b, cl
  or r10b, dl
  or r10b, dil
  or r10b, sil
  or r10b, bpl
  or r10b, spl
  or r10b, r8b
  or r10b, r9b
  or r10b, r10b
  or r10b, r11b
  or r10b, r12b
  or r10b, r13b
  or r10b, r14b
  or r10b, r15b
  or r11b, al
  or r11b, bl
  or r11b, cl
  or r11b, dl
  or r11b, dil
  or r11b, sil
  or r11b, bpl
  or r11b, spl
  or r11b, r8b
  or r11b, r9b
  or r11b, r10b
  or r11b, r11b
  or r11b, r12b
  or r11b, r13b
  or r11b, r14b
  or r11b, r15b
  or r12b, al
  or r12b, bl
  or r12b, cl
  or r12b, dl
  or r12b, dil
  or r12b, sil
  or r12b, bpl
  or r12b, spl
  or r12b, r8b
  or r12b, r9b
  or r12b, r10b
  or r12b, r11b
  or r12b, r12b
  or r12b, r13b
  or r12b, r14b
  or r12b, r15b
  or r13b, al
  or r13b, bl
  or r13b, cl
  or r13b, dl
  or r13b, dil
  or r13b, sil
  or r13b, bpl
  or r13b, spl
  or r13b, r8b
  or r13b, r9b
  or r13b, r10b
  or r13b, r11b
  or r13b, r12b
  or r13b, r13b
  or r13b, r14b
  or r13b, r15b
  or r14b, al
  or r14b, bl
  or r14b, cl
  or r14b, dl
  or r14b, dil
  or r14b, sil
  or r14b, bpl
  or r14b, spl
  or r14b, r8b
  or r14b, r9b
  or r14b, r10b
  or r14b, r11b
  or r14b, r12b
  or r14b, r13b
  or r14b, r14b
  or r14b, r15b
  or r15b, al
  or r15b, bl
  or r15b, cl
  or r15b, dl
  or r15b, dil
  or r15b, sil
  or r15b, bpl
  or r15b, spl
  or r15b, r8b
  or r15b, r9b
  or r15b, r10b
  or r15b, r11b
  or r15b, r12b
  or r15b, r13b
  or r15b, r14b
  or r15b, r15b


; or m8,r8

  or byte [mem8], al
  or byte [mem8], bl
  or byte [mem8], cl
  or byte [mem8], dl
  or byte [mem8], dil
  or byte [mem8], sil
  or byte [mem8], bpl
  or byte [mem8], spl
  or byte [mem8], r8b
  or byte [mem8], r9b
  or byte [mem8], r10b
  or byte [mem8], r11b
  or byte [mem8], r12b
  or byte [mem8], r13b
  or byte [mem8], r14b
  or byte [mem8], r15b


; or r8,m8

  or al, byte [mem8]
  or bl, byte [mem8]
  or cl, byte [mem8]
  or dl, byte [mem8]
  or dil, byte [mem8]
  or sil, byte [mem8]
  or bpl, byte [mem8]
  or spl, byte [mem8]
  or r8b, byte [mem8]
  or r9b, byte [mem8]
  or r10b, byte [mem8]
  or r11b, byte [mem8]
  or r12b, byte [mem8]
  or r13b, byte [mem8]
  or r14b, byte [mem8]
  or r15b, byte [mem8]


; or r8,i8

  or al, imm8
  or bl, imm8
  or cl, imm8
  or dl, imm8
  or dil, imm8
  or sil, imm8
  or bpl, imm8
  or spl, imm8
  or r8b, imm8
  or r9b, imm8
  or r10b, imm8
  or r11b, imm8
  or r12b, imm8
  or r13b, imm8
  or r14b, imm8
  or r15b, imm8


; or m8,i8

  or byte [mem8], imm8


; or r16,r16

  or ax, ax
  or ax, bx
  or ax, cx
  or ax, dx
  or ax, di
  or ax, si
  or ax, bp
  or ax, sp
  or ax, r8w
  or ax, r9w
  or ax, r10w
  or ax, r11w
  or ax, r12w
  or ax, r13w
  or ax, r14w
  or ax, r15w
  or bx, ax
  or bx, bx
  or bx, cx
  or bx, dx
  or bx, di
  or bx, si
  or bx, bp
  or bx, sp
  or bx, r8w
  or bx, r9w
  or bx, r10w
  or bx, r11w
  or bx, r12w
  or bx, r13w
  or bx, r14w
  or bx, r15w
  or cx, ax
  or cx, bx
  or cx, cx
  or cx, dx
  or cx, di
  or cx, si
  or cx, bp
  or cx, sp
  or cx, r8w
  or cx, r9w
  or cx, r10w
  or cx, r11w
  or cx, r12w
  or cx, r13w
  or cx, r14w
  or cx, r15w
  or dx, ax
  or dx, bx
  or dx, cx
  or dx, dx
  or dx, di
  or dx, si
  or dx, bp
  or dx, sp
  or dx, r8w
  or dx, r9w
  or dx, r10w
  or dx, r11w
  or dx, r12w
  or dx, r13w
  or dx, r14w
  or dx, r15w
  or di, ax
  or di, bx
  or di, cx
  or di, dx
  or di, di
  or di, si
  or di, bp
  or di, sp
  or di, r8w
  or di, r9w
  or di, r10w
  or di, r11w
  or di, r12w
  or di, r13w
  or di, r14w
  or di, r15w
  or si, ax
  or si, bx
  or si, cx
  or si, dx
  or si, di
  or si, si
  or si, bp
  or si, sp
  or si, r8w
  or si, r9w
  or si, r10w
  or si, r11w
  or si, r12w
  or si, r13w
  or si, r14w
  or si, r15w
  or bp, ax
  or bp, bx
  or bp, cx
  or bp, dx
  or bp, di
  or bp, si
  or bp, bp
  or bp, sp
  or bp, r8w
  or bp, r9w
  or bp, r10w
  or bp, r11w
  or bp, r12w
  or bp, r13w
  or bp, r14w
  or bp, r15w
  or sp, ax
  or sp, bx
  or sp, cx
  or sp, dx
  or sp, di
  or sp, si
  or sp, bp
  or sp, sp
  or sp, r8w
  or sp, r9w
  or sp, r10w
  or sp, r11w
  or sp, r12w
  or sp, r13w
  or sp, r14w
  or sp, r15w
  or r8w, ax
  or r8w, bx
  or r8w, cx
  or r8w, dx
  or r8w, di
  or r8w, si
  or r8w, bp
  or r8w, sp
  or r8w, r8w
  or r8w, r9w
  or r8w, r10w
  or r8w, r11w
  or r8w, r12w
  or r8w, r13w
  or r8w, r14w
  or r8w, r15w
  or r9w, ax
  or r9w, bx
  or r9w, cx
  or r9w, dx
  or r9w, di
  or r9w, si
  or r9w, bp
  or r9w, sp
  or r9w, r8w
  or r9w, r9w
  or r9w, r10w
  or r9w, r11w
  or r9w, r12w
  or r9w, r13w
  or r9w, r14w
  or r9w, r15w
  or r10w, ax
  or r10w, bx
  or r10w, cx
  or r10w, dx
  or r10w, di
  or r10w, si
  or r10w, bp
  or r10w, sp
  or r10w, r8w
  or r10w, r9w
  or r10w, r10w
  or r10w, r11w
  or r10w, r12w
  or r10w, r13w
  or r10w, r14w
  or r10w, r15w
  or r11w, ax
  or r11w, bx
  or r11w, cx
  or r11w, dx
  or r11w, di
  or r11w, si
  or r11w, bp
  or r11w, sp
  or r11w, r8w
  or r11w, r9w
  or r11w, r10w
  or r11w, r11w
  or r11w, r12w
  or r11w, r13w
  or r11w, r14w
  or r11w, r15w
  or r12w, ax
  or r12w, bx
  or r12w, cx
  or r12w, dx
  or r12w, di
  or r12w, si
  or r12w, bp
  or r12w, sp
  or r12w, r8w
  or r12w, r9w
  or r12w, r10w
  or r12w, r11w
  or r12w, r12w
  or r12w, r13w
  or r12w, r14w
  or r12w, r15w
  or r13w, ax
  or r13w, bx
  or r13w, cx
  or r13w, dx
  or r13w, di
  or r13w, si
  or r13w, bp
  or r13w, sp
  or r13w, r8w
  or r13w, r9w
  or r13w, r10w
  or r13w, r11w
  or r13w, r12w
  or r13w, r13w
  or r13w, r14w
  or r13w, r15w
  or r14w, ax
  or r14w, bx
  or r14w, cx
  or r14w, dx
  or r14w, di
  or r14w, si
  or r14w, bp
  or r14w, sp
  or r14w, r8w
  or r14w, r9w
  or r14w, r10w
  or r14w, r11w
  or r14w, r12w
  or r14w, r13w
  or r14w, r14w
  or r14w, r15w
  or r15w, ax
  or r15w, bx
  or r15w, cx
  or r15w, dx
  or r15w, di
  or r15w, si
  or r15w, bp
  or r15w, sp
  or r15w, r8w
  or r15w, r9w
  or r15w, r10w
  or r15w, r11w
  or r15w, r12w
  or r15w, r13w
  or r15w, r14w
  or r15w, r15w


; or m16,r16

  or word [mem16], ax
  or word [mem16], bx
  or word [mem16], cx
  or word [mem16], dx
  or word [mem16], di
  or word [mem16], si
  or word [mem16], bp
  or word [mem16], sp
  or word [mem16], r8w
  or word [mem16], r9w
  or word [mem16], r10w
  or word [mem16], r11w
  or word [mem16], r12w
  or word [mem16], r13w
  or word [mem16], r14w
  or word [mem16], r15w


; or r16,m16

  or ax, word [mem16]
  or bx, word [mem16]
  or cx, word [mem16]
  or dx, word [mem16]
  or di, word [mem16]
  or si, word [mem16]
  or bp, word [mem16]
  or sp, word [mem16]
  or r8w, word [mem16]
  or r9w, word [mem16]
  or r10w, word [mem16]
  or r11w, word [mem16]
  or r12w, word [mem16]
  or r13w, word [mem16]
  or r14w, word [mem16]
  or r15w, word [mem16]


; or r16,i16

  or ax, imm16
  or bx, imm16
  or cx, imm16
  or dx, imm16
  or di, imm16
  or si, imm16
  or bp, imm16
  or sp, imm16
  or r8w, imm16
  or r9w, imm16
  or r10w, imm16
  or r11w, imm16
  or r12w, imm16
  or r13w, imm16
  or r14w, imm16
  or r15w, imm16


; or m16,i16

  or word [mem16], imm16


; or r32,r32

  or eax, eax
  or eax, ebx
  or eax, ecx
  or eax, edx
  or eax, edi
  or eax, esi
  or eax, ebp
  or eax, esp
  or eax, r8d
  or eax, r9d
  or eax, r10d
  or eax, r11d
  or eax, r12d
  or eax, r13d
  or eax, r14d
  or eax, r15d
  or ebx, eax
  or ebx, ebx
  or ebx, ecx
  or ebx, edx
  or ebx, edi
  or ebx, esi
  or ebx, ebp
  or ebx, esp
  or ebx, r8d
  or ebx, r9d
  or ebx, r10d
  or ebx, r11d
  or ebx, r12d
  or ebx, r13d
  or ebx, r14d
  or ebx, r15d
  or ecx, eax
  or ecx, ebx
  or ecx, ecx
  or ecx, edx
  or ecx, edi
  or ecx, esi
  or ecx, ebp
  or ecx, esp
  or ecx, r8d
  or ecx, r9d
  or ecx, r10d
  or ecx, r11d
  or ecx, r12d
  or ecx, r13d
  or ecx, r14d
  or ecx, r15d
  or edx, eax
  or edx, ebx
  or edx, ecx
  or edx, edx
  or edx, edi
  or edx, esi
  or edx, ebp
  or edx, esp
  or edx, r8d
  or edx, r9d
  or edx, r10d
  or edx, r11d
  or edx, r12d
  or edx, r13d
  or edx, r14d
  or edx, r15d
  or edi, eax
  or edi, ebx
  or edi, ecx
  or edi, edx
  or edi, edi
  or edi, esi
  or edi, ebp
  or edi, esp
  or edi, r8d
  or edi, r9d
  or edi, r10d
  or edi, r11d
  or edi, r12d
  or edi, r13d
  or edi, r14d
  or edi, r15d
  or esi, eax
  or esi, ebx
  or esi, ecx
  or esi, edx
  or esi, edi
  or esi, esi
  or esi, ebp
  or esi, esp
  or esi, r8d
  or esi, r9d
  or esi, r10d
  or esi, r11d
  or esi, r12d
  or esi, r13d
  or esi, r14d
  or esi, r15d
  or ebp, eax
  or ebp, ebx
  or ebp, ecx
  or ebp, edx
  or ebp, edi
  or ebp, esi
  or ebp, ebp
  or ebp, esp
  or ebp, r8d
  or ebp, r9d
  or ebp, r10d
  or ebp, r11d
  or ebp, r12d
  or ebp, r13d
  or ebp, r14d
  or ebp, r15d
  or esp, eax
  or esp, ebx
  or esp, ecx
  or esp, edx
  or esp, edi
  or esp, esi
  or esp, ebp
  or esp, esp
  or esp, r8d
  or esp, r9d
  or esp, r10d
  or esp, r11d
  or esp, r12d
  or esp, r13d
  or esp, r14d
  or esp, r15d
  or r8d, eax
  or r8d, ebx
  or r8d, ecx
  or r8d, edx
  or r8d, edi
  or r8d, esi
  or r8d, ebp
  or r8d, esp
  or r8d, r8d
  or r8d, r9d
  or r8d, r10d
  or r8d, r11d
  or r8d, r12d
  or r8d, r13d
  or r8d, r14d
  or r8d, r15d
  or r9d, eax
  or r9d, ebx
  or r9d, ecx
  or r9d, edx
  or r9d, edi
  or r9d, esi
  or r9d, ebp
  or r9d, esp
  or r9d, r8d
  or r9d, r9d
  or r9d, r10d
  or r9d, r11d
  or r9d, r12d
  or r9d, r13d
  or r9d, r14d
  or r9d, r15d
  or r10d, eax
  or r10d, ebx
  or r10d, ecx
  or r10d, edx
  or r10d, edi
  or r10d, esi
  or r10d, ebp
  or r10d, esp
  or r10d, r8d
  or r10d, r9d
  or r10d, r10d
  or r10d, r11d
  or r10d, r12d
  or r10d, r13d
  or r10d, r14d
  or r10d, r15d
  or r11d, eax
  or r11d, ebx
  or r11d, ecx
  or r11d, edx
  or r11d, edi
  or r11d, esi
  or r11d, ebp
  or r11d, esp
  or r11d, r8d
  or r11d, r9d
  or r11d, r10d
  or r11d, r11d
  or r11d, r12d
  or r11d, r13d
  or r11d, r14d
  or r11d, r15d
  or r12d, eax
  or r12d, ebx
  or r12d, ecx
  or r12d, edx
  or r12d, edi
  or r12d, esi
  or r12d, ebp
  or r12d, esp
  or r12d, r8d
  or r12d, r9d
  or r12d, r10d
  or r12d, r11d
  or r12d, r12d
  or r12d, r13d
  or r12d, r14d
  or r12d, r15d
  or r13d, eax
  or r13d, ebx
  or r13d, ecx
  or r13d, edx
  or r13d, edi
  or r13d, esi
  or r13d, ebp
  or r13d, esp
  or r13d, r8d
  or r13d, r9d
  or r13d, r10d
  or r13d, r11d
  or r13d, r12d
  or r13d, r13d
  or r13d, r14d
  or r13d, r15d
  or r14d, eax
  or r14d, ebx
  or r14d, ecx
  or r14d, edx
  or r14d, edi
  or r14d, esi
  or r14d, ebp
  or r14d, esp
  or r14d, r8d
  or r14d, r9d
  or r14d, r10d
  or r14d, r11d
  or r14d, r12d
  or r14d, r13d
  or r14d, r14d
  or r14d, r15d
  or r15d, eax
  or r15d, ebx
  or r15d, ecx
  or r15d, edx
  or r15d, edi
  or r15d, esi
  or r15d, ebp
  or r15d, esp
  or r15d, r8d
  or r15d, r9d
  or r15d, r10d
  or r15d, r11d
  or r15d, r12d
  or r15d, r13d
  or r15d, r14d
  or r15d, r15d


; or m32,r32

  or dword [mem32], eax
  or dword [mem32], ebx
  or dword [mem32], ecx
  or dword [mem32], edx
  or dword [mem32], edi
  or dword [mem32], esi
  or dword [mem32], ebp
  or dword [mem32], esp
  or dword [mem32], r8d
  or dword [mem32], r9d
  or dword [mem32], r10d
  or dword [mem32], r11d
  or dword [mem32], r12d
  or dword [mem32], r13d
  or dword [mem32], r14d
  or dword [mem32], r15d


; or r32,m32

  or eax, dword [mem32]
  or ebx, dword [mem32]
  or ecx, dword [mem32]
  or edx, dword [mem32]
  or edi, dword [mem32]
  or esi, dword [mem32]
  or ebp, dword [mem32]
  or esp, dword [mem32]
  or r8d, dword [mem32]
  or r9d, dword [mem32]
  or r10d, dword [mem32]
  or r11d, dword [mem32]
  or r12d, dword [mem32]
  or r13d, dword [mem32]
  or r14d, dword [mem32]
  or r15d, dword [mem32]


; or r32,i32

  or eax, imm32
  or ebx, imm32
  or ecx, imm32
  or edx, imm32
  or edi, imm32
  or esi, imm32
  or ebp, imm32
  or esp, imm32
  or r8d, imm32
  or r9d, imm32
  or r10d, imm32
  or r11d, imm32
  or r12d, imm32
  or r13d, imm32
  or r14d, imm32
  or r15d, imm32


; or m32,i32

  or dword [mem32], imm32


; or r64,r64

  or rax, rax
  or rax, rbx
  or rax, rcx
  or rax, rdx
  or rax, rdi
  or rax, rsi
  or rax, rbp
  or rax, rsp
  or rax, r8
  or rax, r9
  or rax, r10
  or rax, r11
  or rax, r12
  or rax, r13
  or rax, r14
  or rax, r15
  or rbx, rax
  or rbx, rbx
  or rbx, rcx
  or rbx, rdx
  or rbx, rdi
  or rbx, rsi
  or rbx, rbp
  or rbx, rsp
  or rbx, r8
  or rbx, r9
  or rbx, r10
  or rbx, r11
  or rbx, r12
  or rbx, r13
  or rbx, r14
  or rbx, r15
  or rcx, rax
  or rcx, rbx
  or rcx, rcx
  or rcx, rdx
  or rcx, rdi
  or rcx, rsi
  or rcx, rbp
  or rcx, rsp
  or rcx, r8
  or rcx, r9
  or rcx, r10
  or rcx, r11
  or rcx, r12
  or rcx, r13
  or rcx, r14
  or rcx, r15
  or rdx, rax
  or rdx, rbx
  or rdx, rcx
  or rdx, rdx
  or rdx, rdi
  or rdx, rsi
  or rdx, rbp
  or rdx, rsp
  or rdx, r8
  or rdx, r9
  or rdx, r10
  or rdx, r11
  or rdx, r12
  or rdx, r13
  or rdx, r14
  or rdx, r15
  or rdi, rax
  or rdi, rbx
  or rdi, rcx
  or rdi, rdx
  or rdi, rdi
  or rdi, rsi
  or rdi, rbp
  or rdi, rsp
  or rdi, r8
  or rdi, r9
  or rdi, r10
  or rdi, r11
  or rdi, r12
  or rdi, r13
  or rdi, r14
  or rdi, r15
  or rsi, rax
  or rsi, rbx
  or rsi, rcx
  or rsi, rdx
  or rsi, rdi
  or rsi, rsi
  or rsi, rbp
  or rsi, rsp
  or rsi, r8
  or rsi, r9
  or rsi, r10
  or rsi, r11
  or rsi, r12
  or rsi, r13
  or rsi, r14
  or rsi, r15
  or rbp, rax
  or rbp, rbx
  or rbp, rcx
  or rbp, rdx
  or rbp, rdi
  or rbp, rsi
  or rbp, rbp
  or rbp, rsp
  or rbp, r8
  or rbp, r9
  or rbp, r10
  or rbp, r11
  or rbp, r12
  or rbp, r13
  or rbp, r14
  or rbp, r15
  or rsp, rax
  or rsp, rbx
  or rsp, rcx
  or rsp, rdx
  or rsp, rdi
  or rsp, rsi
  or rsp, rbp
  or rsp, rsp
  or rsp, r8
  or rsp, r9
  or rsp, r10
  or rsp, r11
  or rsp, r12
  or rsp, r13
  or rsp, r14
  or rsp, r15
  or r8, rax
  or r8, rbx
  or r8, rcx
  or r8, rdx
  or r8, rdi
  or r8, rsi
  or r8, rbp
  or r8, rsp
  or r8, r8
  or r8, r9
  or r8, r10
  or r8, r11
  or r8, r12
  or r8, r13
  or r8, r14
  or r8, r15
  or r9, rax
  or r9, rbx
  or r9, rcx
  or r9, rdx
  or r9, rdi
  or r9, rsi
  or r9, rbp
  or r9, rsp
  or r9, r8
  or r9, r9
  or r9, r10
  or r9, r11
  or r9, r12
  or r9, r13
  or r9, r14
  or r9, r15
  or r10, rax
  or r10, rbx
  or r10, rcx
  or r10, rdx
  or r10, rdi
  or r10, rsi
  or r10, rbp
  or r10, rsp
  or r10, r8
  or r10, r9
  or r10, r10
  or r10, r11
  or r10, r12
  or r10, r13
  or r10, r14
  or r10, r15
  or r11, rax
  or r11, rbx
  or r11, rcx
  or r11, rdx
  or r11, rdi
  or r11, rsi
  or r11, rbp
  or r11, rsp
  or r11, r8
  or r11, r9
  or r11, r10
  or r11, r11
  or r11, r12
  or r11, r13
  or r11, r14
  or r11, r15
  or r12, rax
  or r12, rbx
  or r12, rcx
  or r12, rdx
  or r12, rdi
  or r12, rsi
  or r12, rbp
  or r12, rsp
  or r12, r8
  or r12, r9
  or r12, r10
  or r12, r11
  or r12, r12
  or r12, r13
  or r12, r14
  or r12, r15
  or r13, rax
  or r13, rbx
  or r13, rcx
  or r13, rdx
  or r13, rdi
  or r13, rsi
  or r13, rbp
  or r13, rsp
  or r13, r8
  or r13, r9
  or r13, r10
  or r13, r11
  or r13, r12
  or r13, r13
  or r13, r14
  or r13, r15
  or r14, rax
  or r14, rbx
  or r14, rcx
  or r14, rdx
  or r14, rdi
  or r14, rsi
  or r14, rbp
  or r14, rsp
  or r14, r8
  or r14, r9
  or r14, r10
  or r14, r11
  or r14, r12
  or r14, r13
  or r14, r14
  or r14, r15
  or r15, rax
  or r15, rbx
  or r15, rcx
  or r15, rdx
  or r15, rdi
  or r15, rsi
  or r15, rbp
  or r15, rsp
  or r15, r8
  or r15, r9
  or r15, r10
  or r15, r11
  or r15, r12
  or r15, r13
  or r15, r14
  or r15, r15


; or m64,r64

  or qword [mem64], rax
  or qword [mem64], rbx
  or qword [mem64], rcx
  or qword [mem64], rdx
  or qword [mem64], rdi
  or qword [mem64], rsi
  or qword [mem64], rbp
  or qword [mem64], rsp
  or qword [mem64], r8
  or qword [mem64], r9
  or qword [mem64], r10
  or qword [mem64], r11
  or qword [mem64], r12
  or qword [mem64], r13
  or qword [mem64], r14
  or qword [mem64], r15


; or r64,m64

  or rax, qword [mem64]
  or rbx, qword [mem64]
  or rcx, qword [mem64]
  or rdx, qword [mem64]
  or rdi, qword [mem64]
  or rsi, qword [mem64]
  or rbp, qword [mem64]
  or rsp, qword [mem64]
  or r8, qword [mem64]
  or r9, qword [mem64]
  or r10, qword [mem64]
  or r11, qword [mem64]
  or r12, qword [mem64]
  or r13, qword [mem64]
  or r14, qword [mem64]
  or r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
