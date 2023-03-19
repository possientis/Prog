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

; cmp r8,r8

  cmp al, al
  cmp al, bl
  cmp al, cl
  cmp al, dl
  cmp al, dil
  cmp al, sil
  cmp al, bpl
  cmp al, spl
  cmp al, r8b
  cmp al, r9b
  cmp al, r10b
  cmp al, r11b
  cmp al, r12b
  cmp al, r13b
  cmp al, r14b
  cmp al, r15b
  cmp bl, al
  cmp bl, bl
  cmp bl, cl
  cmp bl, dl
  cmp bl, dil
  cmp bl, sil
  cmp bl, bpl
  cmp bl, spl
  cmp bl, r8b
  cmp bl, r9b
  cmp bl, r10b
  cmp bl, r11b
  cmp bl, r12b
  cmp bl, r13b
  cmp bl, r14b
  cmp bl, r15b
  cmp cl, al
  cmp cl, bl
  cmp cl, cl
  cmp cl, dl
  cmp cl, dil
  cmp cl, sil
  cmp cl, bpl
  cmp cl, spl
  cmp cl, r8b
  cmp cl, r9b
  cmp cl, r10b
  cmp cl, r11b
  cmp cl, r12b
  cmp cl, r13b
  cmp cl, r14b
  cmp cl, r15b
  cmp dl, al
  cmp dl, bl
  cmp dl, cl
  cmp dl, dl
  cmp dl, dil
  cmp dl, sil
  cmp dl, bpl
  cmp dl, spl
  cmp dl, r8b
  cmp dl, r9b
  cmp dl, r10b
  cmp dl, r11b
  cmp dl, r12b
  cmp dl, r13b
  cmp dl, r14b
  cmp dl, r15b
  cmp dil, al
  cmp dil, bl
  cmp dil, cl
  cmp dil, dl
  cmp dil, dil
  cmp dil, sil
  cmp dil, bpl
  cmp dil, spl
  cmp dil, r8b
  cmp dil, r9b
  cmp dil, r10b
  cmp dil, r11b
  cmp dil, r12b
  cmp dil, r13b
  cmp dil, r14b
  cmp dil, r15b
  cmp sil, al
  cmp sil, bl
  cmp sil, cl
  cmp sil, dl
  cmp sil, dil
  cmp sil, sil
  cmp sil, bpl
  cmp sil, spl
  cmp sil, r8b
  cmp sil, r9b
  cmp sil, r10b
  cmp sil, r11b
  cmp sil, r12b
  cmp sil, r13b
  cmp sil, r14b
  cmp sil, r15b
  cmp bpl, al
  cmp bpl, bl
  cmp bpl, cl
  cmp bpl, dl
  cmp bpl, dil
  cmp bpl, sil
  cmp bpl, bpl
  cmp bpl, spl
  cmp bpl, r8b
  cmp bpl, r9b
  cmp bpl, r10b
  cmp bpl, r11b
  cmp bpl, r12b
  cmp bpl, r13b
  cmp bpl, r14b
  cmp bpl, r15b
  cmp spl, al
  cmp spl, bl
  cmp spl, cl
  cmp spl, dl
  cmp spl, dil
  cmp spl, sil
  cmp spl, bpl
  cmp spl, spl
  cmp spl, r8b
  cmp spl, r9b
  cmp spl, r10b
  cmp spl, r11b
  cmp spl, r12b
  cmp spl, r13b
  cmp spl, r14b
  cmp spl, r15b
  cmp r8b, al
  cmp r8b, bl
  cmp r8b, cl
  cmp r8b, dl
  cmp r8b, dil
  cmp r8b, sil
  cmp r8b, bpl
  cmp r8b, spl
  cmp r8b, r8b
  cmp r8b, r9b
  cmp r8b, r10b
  cmp r8b, r11b
  cmp r8b, r12b
  cmp r8b, r13b
  cmp r8b, r14b
  cmp r8b, r15b
  cmp r9b, al
  cmp r9b, bl
  cmp r9b, cl
  cmp r9b, dl
  cmp r9b, dil
  cmp r9b, sil
  cmp r9b, bpl
  cmp r9b, spl
  cmp r9b, r8b
  cmp r9b, r9b
  cmp r9b, r10b
  cmp r9b, r11b
  cmp r9b, r12b
  cmp r9b, r13b
  cmp r9b, r14b
  cmp r9b, r15b
  cmp r10b, al
  cmp r10b, bl
  cmp r10b, cl
  cmp r10b, dl
  cmp r10b, dil
  cmp r10b, sil
  cmp r10b, bpl
  cmp r10b, spl
  cmp r10b, r8b
  cmp r10b, r9b
  cmp r10b, r10b
  cmp r10b, r11b
  cmp r10b, r12b
  cmp r10b, r13b
  cmp r10b, r14b
  cmp r10b, r15b
  cmp r11b, al
  cmp r11b, bl
  cmp r11b, cl
  cmp r11b, dl
  cmp r11b, dil
  cmp r11b, sil
  cmp r11b, bpl
  cmp r11b, spl
  cmp r11b, r8b
  cmp r11b, r9b
  cmp r11b, r10b
  cmp r11b, r11b
  cmp r11b, r12b
  cmp r11b, r13b
  cmp r11b, r14b
  cmp r11b, r15b
  cmp r12b, al
  cmp r12b, bl
  cmp r12b, cl
  cmp r12b, dl
  cmp r12b, dil
  cmp r12b, sil
  cmp r12b, bpl
  cmp r12b, spl
  cmp r12b, r8b
  cmp r12b, r9b
  cmp r12b, r10b
  cmp r12b, r11b
  cmp r12b, r12b
  cmp r12b, r13b
  cmp r12b, r14b
  cmp r12b, r15b
  cmp r13b, al
  cmp r13b, bl
  cmp r13b, cl
  cmp r13b, dl
  cmp r13b, dil
  cmp r13b, sil
  cmp r13b, bpl
  cmp r13b, spl
  cmp r13b, r8b
  cmp r13b, r9b
  cmp r13b, r10b
  cmp r13b, r11b
  cmp r13b, r12b
  cmp r13b, r13b
  cmp r13b, r14b
  cmp r13b, r15b
  cmp r14b, al
  cmp r14b, bl
  cmp r14b, cl
  cmp r14b, dl
  cmp r14b, dil
  cmp r14b, sil
  cmp r14b, bpl
  cmp r14b, spl
  cmp r14b, r8b
  cmp r14b, r9b
  cmp r14b, r10b
  cmp r14b, r11b
  cmp r14b, r12b
  cmp r14b, r13b
  cmp r14b, r14b
  cmp r14b, r15b
  cmp r15b, al
  cmp r15b, bl
  cmp r15b, cl
  cmp r15b, dl
  cmp r15b, dil
  cmp r15b, sil
  cmp r15b, bpl
  cmp r15b, spl
  cmp r15b, r8b
  cmp r15b, r9b
  cmp r15b, r10b
  cmp r15b, r11b
  cmp r15b, r12b
  cmp r15b, r13b
  cmp r15b, r14b
  cmp r15b, r15b


; cmp m8,r8

  cmp byte [mem8], al
  cmp byte [mem8], bl
  cmp byte [mem8], cl
  cmp byte [mem8], dl
  cmp byte [mem8], dil
  cmp byte [mem8], sil
  cmp byte [mem8], bpl
  cmp byte [mem8], spl
  cmp byte [mem8], r8b
  cmp byte [mem8], r9b
  cmp byte [mem8], r10b
  cmp byte [mem8], r11b
  cmp byte [mem8], r12b
  cmp byte [mem8], r13b
  cmp byte [mem8], r14b
  cmp byte [mem8], r15b


; cmp r8,m8

  cmp al, byte [mem8]
  cmp bl, byte [mem8]
  cmp cl, byte [mem8]
  cmp dl, byte [mem8]
  cmp dil, byte [mem8]
  cmp sil, byte [mem8]
  cmp bpl, byte [mem8]
  cmp spl, byte [mem8]
  cmp r8b, byte [mem8]
  cmp r9b, byte [mem8]
  cmp r10b, byte [mem8]
  cmp r11b, byte [mem8]
  cmp r12b, byte [mem8]
  cmp r13b, byte [mem8]
  cmp r14b, byte [mem8]
  cmp r15b, byte [mem8]


; cmp r8,i8

  cmp al, imm8
  cmp bl, imm8
  cmp cl, imm8
  cmp dl, imm8
  cmp dil, imm8
  cmp sil, imm8
  cmp bpl, imm8
  cmp spl, imm8
  cmp r8b, imm8
  cmp r9b, imm8
  cmp r10b, imm8
  cmp r11b, imm8
  cmp r12b, imm8
  cmp r13b, imm8
  cmp r14b, imm8
  cmp r15b, imm8


; cmp m8,i8

  cmp byte [mem8], imm8


; cmp r16,r16

  cmp ax, ax
  cmp ax, bx
  cmp ax, cx
  cmp ax, dx
  cmp ax, di
  cmp ax, si
  cmp ax, bp
  cmp ax, sp
  cmp ax, r8w
  cmp ax, r9w
  cmp ax, r10w
  cmp ax, r11w
  cmp ax, r12w
  cmp ax, r13w
  cmp ax, r14w
  cmp ax, r15w
  cmp bx, ax
  cmp bx, bx
  cmp bx, cx
  cmp bx, dx
  cmp bx, di
  cmp bx, si
  cmp bx, bp
  cmp bx, sp
  cmp bx, r8w
  cmp bx, r9w
  cmp bx, r10w
  cmp bx, r11w
  cmp bx, r12w
  cmp bx, r13w
  cmp bx, r14w
  cmp bx, r15w
  cmp cx, ax
  cmp cx, bx
  cmp cx, cx
  cmp cx, dx
  cmp cx, di
  cmp cx, si
  cmp cx, bp
  cmp cx, sp
  cmp cx, r8w
  cmp cx, r9w
  cmp cx, r10w
  cmp cx, r11w
  cmp cx, r12w
  cmp cx, r13w
  cmp cx, r14w
  cmp cx, r15w
  cmp dx, ax
  cmp dx, bx
  cmp dx, cx
  cmp dx, dx
  cmp dx, di
  cmp dx, si
  cmp dx, bp
  cmp dx, sp
  cmp dx, r8w
  cmp dx, r9w
  cmp dx, r10w
  cmp dx, r11w
  cmp dx, r12w
  cmp dx, r13w
  cmp dx, r14w
  cmp dx, r15w
  cmp di, ax
  cmp di, bx
  cmp di, cx
  cmp di, dx
  cmp di, di
  cmp di, si
  cmp di, bp
  cmp di, sp
  cmp di, r8w
  cmp di, r9w
  cmp di, r10w
  cmp di, r11w
  cmp di, r12w
  cmp di, r13w
  cmp di, r14w
  cmp di, r15w
  cmp si, ax
  cmp si, bx
  cmp si, cx
  cmp si, dx
  cmp si, di
  cmp si, si
  cmp si, bp
  cmp si, sp
  cmp si, r8w
  cmp si, r9w
  cmp si, r10w
  cmp si, r11w
  cmp si, r12w
  cmp si, r13w
  cmp si, r14w
  cmp si, r15w
  cmp bp, ax
  cmp bp, bx
  cmp bp, cx
  cmp bp, dx
  cmp bp, di
  cmp bp, si
  cmp bp, bp
  cmp bp, sp
  cmp bp, r8w
  cmp bp, r9w
  cmp bp, r10w
  cmp bp, r11w
  cmp bp, r12w
  cmp bp, r13w
  cmp bp, r14w
  cmp bp, r15w
  cmp sp, ax
  cmp sp, bx
  cmp sp, cx
  cmp sp, dx
  cmp sp, di
  cmp sp, si
  cmp sp, bp
  cmp sp, sp
  cmp sp, r8w
  cmp sp, r9w
  cmp sp, r10w
  cmp sp, r11w
  cmp sp, r12w
  cmp sp, r13w
  cmp sp, r14w
  cmp sp, r15w
  cmp r8w, ax
  cmp r8w, bx
  cmp r8w, cx
  cmp r8w, dx
  cmp r8w, di
  cmp r8w, si
  cmp r8w, bp
  cmp r8w, sp
  cmp r8w, r8w
  cmp r8w, r9w
  cmp r8w, r10w
  cmp r8w, r11w
  cmp r8w, r12w
  cmp r8w, r13w
  cmp r8w, r14w
  cmp r8w, r15w
  cmp r9w, ax
  cmp r9w, bx
  cmp r9w, cx
  cmp r9w, dx
  cmp r9w, di
  cmp r9w, si
  cmp r9w, bp
  cmp r9w, sp
  cmp r9w, r8w
  cmp r9w, r9w
  cmp r9w, r10w
  cmp r9w, r11w
  cmp r9w, r12w
  cmp r9w, r13w
  cmp r9w, r14w
  cmp r9w, r15w
  cmp r10w, ax
  cmp r10w, bx
  cmp r10w, cx
  cmp r10w, dx
  cmp r10w, di
  cmp r10w, si
  cmp r10w, bp
  cmp r10w, sp
  cmp r10w, r8w
  cmp r10w, r9w
  cmp r10w, r10w
  cmp r10w, r11w
  cmp r10w, r12w
  cmp r10w, r13w
  cmp r10w, r14w
  cmp r10w, r15w
  cmp r11w, ax
  cmp r11w, bx
  cmp r11w, cx
  cmp r11w, dx
  cmp r11w, di
  cmp r11w, si
  cmp r11w, bp
  cmp r11w, sp
  cmp r11w, r8w
  cmp r11w, r9w
  cmp r11w, r10w
  cmp r11w, r11w
  cmp r11w, r12w
  cmp r11w, r13w
  cmp r11w, r14w
  cmp r11w, r15w
  cmp r12w, ax
  cmp r12w, bx
  cmp r12w, cx
  cmp r12w, dx
  cmp r12w, di
  cmp r12w, si
  cmp r12w, bp
  cmp r12w, sp
  cmp r12w, r8w
  cmp r12w, r9w
  cmp r12w, r10w
  cmp r12w, r11w
  cmp r12w, r12w
  cmp r12w, r13w
  cmp r12w, r14w
  cmp r12w, r15w
  cmp r13w, ax
  cmp r13w, bx
  cmp r13w, cx
  cmp r13w, dx
  cmp r13w, di
  cmp r13w, si
  cmp r13w, bp
  cmp r13w, sp
  cmp r13w, r8w
  cmp r13w, r9w
  cmp r13w, r10w
  cmp r13w, r11w
  cmp r13w, r12w
  cmp r13w, r13w
  cmp r13w, r14w
  cmp r13w, r15w
  cmp r14w, ax
  cmp r14w, bx
  cmp r14w, cx
  cmp r14w, dx
  cmp r14w, di
  cmp r14w, si
  cmp r14w, bp
  cmp r14w, sp
  cmp r14w, r8w
  cmp r14w, r9w
  cmp r14w, r10w
  cmp r14w, r11w
  cmp r14w, r12w
  cmp r14w, r13w
  cmp r14w, r14w
  cmp r14w, r15w
  cmp r15w, ax
  cmp r15w, bx
  cmp r15w, cx
  cmp r15w, dx
  cmp r15w, di
  cmp r15w, si
  cmp r15w, bp
  cmp r15w, sp
  cmp r15w, r8w
  cmp r15w, r9w
  cmp r15w, r10w
  cmp r15w, r11w
  cmp r15w, r12w
  cmp r15w, r13w
  cmp r15w, r14w
  cmp r15w, r15w


; cmp m16,r16

  cmp word [mem16], ax
  cmp word [mem16], bx
  cmp word [mem16], cx
  cmp word [mem16], dx
  cmp word [mem16], di
  cmp word [mem16], si
  cmp word [mem16], bp
  cmp word [mem16], sp
  cmp word [mem16], r8w
  cmp word [mem16], r9w
  cmp word [mem16], r10w
  cmp word [mem16], r11w
  cmp word [mem16], r12w
  cmp word [mem16], r13w
  cmp word [mem16], r14w
  cmp word [mem16], r15w


; cmp r16,m16

  cmp ax, word [mem16]
  cmp bx, word [mem16]
  cmp cx, word [mem16]
  cmp dx, word [mem16]
  cmp di, word [mem16]
  cmp si, word [mem16]
  cmp bp, word [mem16]
  cmp sp, word [mem16]
  cmp r8w, word [mem16]
  cmp r9w, word [mem16]
  cmp r10w, word [mem16]
  cmp r11w, word [mem16]
  cmp r12w, word [mem16]
  cmp r13w, word [mem16]
  cmp r14w, word [mem16]
  cmp r15w, word [mem16]


; cmp r16,i16

  cmp ax, imm16
  cmp bx, imm16
  cmp cx, imm16
  cmp dx, imm16
  cmp di, imm16
  cmp si, imm16
  cmp bp, imm16
  cmp sp, imm16
  cmp r8w, imm16
  cmp r9w, imm16
  cmp r10w, imm16
  cmp r11w, imm16
  cmp r12w, imm16
  cmp r13w, imm16
  cmp r14w, imm16
  cmp r15w, imm16


; cmp m16,i16

  cmp word [mem16], imm16


; cmp r32,r32

  cmp eax, eax
  cmp eax, ebx
  cmp eax, ecx
  cmp eax, edx
  cmp eax, edi
  cmp eax, esi
  cmp eax, ebp
  cmp eax, esp
  cmp eax, r8d
  cmp eax, r9d
  cmp eax, r10d
  cmp eax, r11d
  cmp eax, r12d
  cmp eax, r13d
  cmp eax, r14d
  cmp eax, r15d
  cmp ebx, eax
  cmp ebx, ebx
  cmp ebx, ecx
  cmp ebx, edx
  cmp ebx, edi
  cmp ebx, esi
  cmp ebx, ebp
  cmp ebx, esp
  cmp ebx, r8d
  cmp ebx, r9d
  cmp ebx, r10d
  cmp ebx, r11d
  cmp ebx, r12d
  cmp ebx, r13d
  cmp ebx, r14d
  cmp ebx, r15d
  cmp ecx, eax
  cmp ecx, ebx
  cmp ecx, ecx
  cmp ecx, edx
  cmp ecx, edi
  cmp ecx, esi
  cmp ecx, ebp
  cmp ecx, esp
  cmp ecx, r8d
  cmp ecx, r9d
  cmp ecx, r10d
  cmp ecx, r11d
  cmp ecx, r12d
  cmp ecx, r13d
  cmp ecx, r14d
  cmp ecx, r15d
  cmp edx, eax
  cmp edx, ebx
  cmp edx, ecx
  cmp edx, edx
  cmp edx, edi
  cmp edx, esi
  cmp edx, ebp
  cmp edx, esp
  cmp edx, r8d
  cmp edx, r9d
  cmp edx, r10d
  cmp edx, r11d
  cmp edx, r12d
  cmp edx, r13d
  cmp edx, r14d
  cmp edx, r15d
  cmp edi, eax
  cmp edi, ebx
  cmp edi, ecx
  cmp edi, edx
  cmp edi, edi
  cmp edi, esi
  cmp edi, ebp
  cmp edi, esp
  cmp edi, r8d
  cmp edi, r9d
  cmp edi, r10d
  cmp edi, r11d
  cmp edi, r12d
  cmp edi, r13d
  cmp edi, r14d
  cmp edi, r15d
  cmp esi, eax
  cmp esi, ebx
  cmp esi, ecx
  cmp esi, edx
  cmp esi, edi
  cmp esi, esi
  cmp esi, ebp
  cmp esi, esp
  cmp esi, r8d
  cmp esi, r9d
  cmp esi, r10d
  cmp esi, r11d
  cmp esi, r12d
  cmp esi, r13d
  cmp esi, r14d
  cmp esi, r15d
  cmp ebp, eax
  cmp ebp, ebx
  cmp ebp, ecx
  cmp ebp, edx
  cmp ebp, edi
  cmp ebp, esi
  cmp ebp, ebp
  cmp ebp, esp
  cmp ebp, r8d
  cmp ebp, r9d
  cmp ebp, r10d
  cmp ebp, r11d
  cmp ebp, r12d
  cmp ebp, r13d
  cmp ebp, r14d
  cmp ebp, r15d
  cmp esp, eax
  cmp esp, ebx
  cmp esp, ecx
  cmp esp, edx
  cmp esp, edi
  cmp esp, esi
  cmp esp, ebp
  cmp esp, esp
  cmp esp, r8d
  cmp esp, r9d
  cmp esp, r10d
  cmp esp, r11d
  cmp esp, r12d
  cmp esp, r13d
  cmp esp, r14d
  cmp esp, r15d
  cmp r8d, eax
  cmp r8d, ebx
  cmp r8d, ecx
  cmp r8d, edx
  cmp r8d, edi
  cmp r8d, esi
  cmp r8d, ebp
  cmp r8d, esp
  cmp r8d, r8d
  cmp r8d, r9d
  cmp r8d, r10d
  cmp r8d, r11d
  cmp r8d, r12d
  cmp r8d, r13d
  cmp r8d, r14d
  cmp r8d, r15d
  cmp r9d, eax
  cmp r9d, ebx
  cmp r9d, ecx
  cmp r9d, edx
  cmp r9d, edi
  cmp r9d, esi
  cmp r9d, ebp
  cmp r9d, esp
  cmp r9d, r8d
  cmp r9d, r9d
  cmp r9d, r10d
  cmp r9d, r11d
  cmp r9d, r12d
  cmp r9d, r13d
  cmp r9d, r14d
  cmp r9d, r15d
  cmp r10d, eax
  cmp r10d, ebx
  cmp r10d, ecx
  cmp r10d, edx
  cmp r10d, edi
  cmp r10d, esi
  cmp r10d, ebp
  cmp r10d, esp
  cmp r10d, r8d
  cmp r10d, r9d
  cmp r10d, r10d
  cmp r10d, r11d
  cmp r10d, r12d
  cmp r10d, r13d
  cmp r10d, r14d
  cmp r10d, r15d
  cmp r11d, eax
  cmp r11d, ebx
  cmp r11d, ecx
  cmp r11d, edx
  cmp r11d, edi
  cmp r11d, esi
  cmp r11d, ebp
  cmp r11d, esp
  cmp r11d, r8d
  cmp r11d, r9d
  cmp r11d, r10d
  cmp r11d, r11d
  cmp r11d, r12d
  cmp r11d, r13d
  cmp r11d, r14d
  cmp r11d, r15d
  cmp r12d, eax
  cmp r12d, ebx
  cmp r12d, ecx
  cmp r12d, edx
  cmp r12d, edi
  cmp r12d, esi
  cmp r12d, ebp
  cmp r12d, esp
  cmp r12d, r8d
  cmp r12d, r9d
  cmp r12d, r10d
  cmp r12d, r11d
  cmp r12d, r12d
  cmp r12d, r13d
  cmp r12d, r14d
  cmp r12d, r15d
  cmp r13d, eax
  cmp r13d, ebx
  cmp r13d, ecx
  cmp r13d, edx
  cmp r13d, edi
  cmp r13d, esi
  cmp r13d, ebp
  cmp r13d, esp
  cmp r13d, r8d
  cmp r13d, r9d
  cmp r13d, r10d
  cmp r13d, r11d
  cmp r13d, r12d
  cmp r13d, r13d
  cmp r13d, r14d
  cmp r13d, r15d
  cmp r14d, eax
  cmp r14d, ebx
  cmp r14d, ecx
  cmp r14d, edx
  cmp r14d, edi
  cmp r14d, esi
  cmp r14d, ebp
  cmp r14d, esp
  cmp r14d, r8d
  cmp r14d, r9d
  cmp r14d, r10d
  cmp r14d, r11d
  cmp r14d, r12d
  cmp r14d, r13d
  cmp r14d, r14d
  cmp r14d, r15d
  cmp r15d, eax
  cmp r15d, ebx
  cmp r15d, ecx
  cmp r15d, edx
  cmp r15d, edi
  cmp r15d, esi
  cmp r15d, ebp
  cmp r15d, esp
  cmp r15d, r8d
  cmp r15d, r9d
  cmp r15d, r10d
  cmp r15d, r11d
  cmp r15d, r12d
  cmp r15d, r13d
  cmp r15d, r14d
  cmp r15d, r15d


; cmp m32,r32

  cmp dword [mem32], eax
  cmp dword [mem32], ebx
  cmp dword [mem32], ecx
  cmp dword [mem32], edx
  cmp dword [mem32], edi
  cmp dword [mem32], esi
  cmp dword [mem32], ebp
  cmp dword [mem32], esp
  cmp dword [mem32], r8d
  cmp dword [mem32], r9d
  cmp dword [mem32], r10d
  cmp dword [mem32], r11d
  cmp dword [mem32], r12d
  cmp dword [mem32], r13d
  cmp dword [mem32], r14d
  cmp dword [mem32], r15d


; cmp r32,m32

  cmp eax, dword [mem32]
  cmp ebx, dword [mem32]
  cmp ecx, dword [mem32]
  cmp edx, dword [mem32]
  cmp edi, dword [mem32]
  cmp esi, dword [mem32]
  cmp ebp, dword [mem32]
  cmp esp, dword [mem32]
  cmp r8d, dword [mem32]
  cmp r9d, dword [mem32]
  cmp r10d, dword [mem32]
  cmp r11d, dword [mem32]
  cmp r12d, dword [mem32]
  cmp r13d, dword [mem32]
  cmp r14d, dword [mem32]
  cmp r15d, dword [mem32]


; cmp r32,i32

  cmp eax, imm32
  cmp ebx, imm32
  cmp ecx, imm32
  cmp edx, imm32
  cmp edi, imm32
  cmp esi, imm32
  cmp ebp, imm32
  cmp esp, imm32
  cmp r8d, imm32
  cmp r9d, imm32
  cmp r10d, imm32
  cmp r11d, imm32
  cmp r12d, imm32
  cmp r13d, imm32
  cmp r14d, imm32
  cmp r15d, imm32


; cmp m32,i32

  cmp dword [mem32], imm32


; cmp r64,r64

  cmp rax, rax
  cmp rax, rbx
  cmp rax, rcx
  cmp rax, rdx
  cmp rax, rdi
  cmp rax, rsi
  cmp rax, rbp
  cmp rax, rsp
  cmp rax, r8
  cmp rax, r9
  cmp rax, r10
  cmp rax, r11
  cmp rax, r12
  cmp rax, r13
  cmp rax, r14
  cmp rax, r15
  cmp rbx, rax
  cmp rbx, rbx
  cmp rbx, rcx
  cmp rbx, rdx
  cmp rbx, rdi
  cmp rbx, rsi
  cmp rbx, rbp
  cmp rbx, rsp
  cmp rbx, r8
  cmp rbx, r9
  cmp rbx, r10
  cmp rbx, r11
  cmp rbx, r12
  cmp rbx, r13
  cmp rbx, r14
  cmp rbx, r15
  cmp rcx, rax
  cmp rcx, rbx
  cmp rcx, rcx
  cmp rcx, rdx
  cmp rcx, rdi
  cmp rcx, rsi
  cmp rcx, rbp
  cmp rcx, rsp
  cmp rcx, r8
  cmp rcx, r9
  cmp rcx, r10
  cmp rcx, r11
  cmp rcx, r12
  cmp rcx, r13
  cmp rcx, r14
  cmp rcx, r15
  cmp rdx, rax
  cmp rdx, rbx
  cmp rdx, rcx
  cmp rdx, rdx
  cmp rdx, rdi
  cmp rdx, rsi
  cmp rdx, rbp
  cmp rdx, rsp
  cmp rdx, r8
  cmp rdx, r9
  cmp rdx, r10
  cmp rdx, r11
  cmp rdx, r12
  cmp rdx, r13
  cmp rdx, r14
  cmp rdx, r15
  cmp rdi, rax
  cmp rdi, rbx
  cmp rdi, rcx
  cmp rdi, rdx
  cmp rdi, rdi
  cmp rdi, rsi
  cmp rdi, rbp
  cmp rdi, rsp
  cmp rdi, r8
  cmp rdi, r9
  cmp rdi, r10
  cmp rdi, r11
  cmp rdi, r12
  cmp rdi, r13
  cmp rdi, r14
  cmp rdi, r15
  cmp rsi, rax
  cmp rsi, rbx
  cmp rsi, rcx
  cmp rsi, rdx
  cmp rsi, rdi
  cmp rsi, rsi
  cmp rsi, rbp
  cmp rsi, rsp
  cmp rsi, r8
  cmp rsi, r9
  cmp rsi, r10
  cmp rsi, r11
  cmp rsi, r12
  cmp rsi, r13
  cmp rsi, r14
  cmp rsi, r15
  cmp rbp, rax
  cmp rbp, rbx
  cmp rbp, rcx
  cmp rbp, rdx
  cmp rbp, rdi
  cmp rbp, rsi
  cmp rbp, rbp
  cmp rbp, rsp
  cmp rbp, r8
  cmp rbp, r9
  cmp rbp, r10
  cmp rbp, r11
  cmp rbp, r12
  cmp rbp, r13
  cmp rbp, r14
  cmp rbp, r15
  cmp rsp, rax
  cmp rsp, rbx
  cmp rsp, rcx
  cmp rsp, rdx
  cmp rsp, rdi
  cmp rsp, rsi
  cmp rsp, rbp
  cmp rsp, rsp
  cmp rsp, r8
  cmp rsp, r9
  cmp rsp, r10
  cmp rsp, r11
  cmp rsp, r12
  cmp rsp, r13
  cmp rsp, r14
  cmp rsp, r15
  cmp r8, rax
  cmp r8, rbx
  cmp r8, rcx
  cmp r8, rdx
  cmp r8, rdi
  cmp r8, rsi
  cmp r8, rbp
  cmp r8, rsp
  cmp r8, r8
  cmp r8, r9
  cmp r8, r10
  cmp r8, r11
  cmp r8, r12
  cmp r8, r13
  cmp r8, r14
  cmp r8, r15
  cmp r9, rax
  cmp r9, rbx
  cmp r9, rcx
  cmp r9, rdx
  cmp r9, rdi
  cmp r9, rsi
  cmp r9, rbp
  cmp r9, rsp
  cmp r9, r8
  cmp r9, r9
  cmp r9, r10
  cmp r9, r11
  cmp r9, r12
  cmp r9, r13
  cmp r9, r14
  cmp r9, r15
  cmp r10, rax
  cmp r10, rbx
  cmp r10, rcx
  cmp r10, rdx
  cmp r10, rdi
  cmp r10, rsi
  cmp r10, rbp
  cmp r10, rsp
  cmp r10, r8
  cmp r10, r9
  cmp r10, r10
  cmp r10, r11
  cmp r10, r12
  cmp r10, r13
  cmp r10, r14
  cmp r10, r15
  cmp r11, rax
  cmp r11, rbx
  cmp r11, rcx
  cmp r11, rdx
  cmp r11, rdi
  cmp r11, rsi
  cmp r11, rbp
  cmp r11, rsp
  cmp r11, r8
  cmp r11, r9
  cmp r11, r10
  cmp r11, r11
  cmp r11, r12
  cmp r11, r13
  cmp r11, r14
  cmp r11, r15
  cmp r12, rax
  cmp r12, rbx
  cmp r12, rcx
  cmp r12, rdx
  cmp r12, rdi
  cmp r12, rsi
  cmp r12, rbp
  cmp r12, rsp
  cmp r12, r8
  cmp r12, r9
  cmp r12, r10
  cmp r12, r11
  cmp r12, r12
  cmp r12, r13
  cmp r12, r14
  cmp r12, r15
  cmp r13, rax
  cmp r13, rbx
  cmp r13, rcx
  cmp r13, rdx
  cmp r13, rdi
  cmp r13, rsi
  cmp r13, rbp
  cmp r13, rsp
  cmp r13, r8
  cmp r13, r9
  cmp r13, r10
  cmp r13, r11
  cmp r13, r12
  cmp r13, r13
  cmp r13, r14
  cmp r13, r15
  cmp r14, rax
  cmp r14, rbx
  cmp r14, rcx
  cmp r14, rdx
  cmp r14, rdi
  cmp r14, rsi
  cmp r14, rbp
  cmp r14, rsp
  cmp r14, r8
  cmp r14, r9
  cmp r14, r10
  cmp r14, r11
  cmp r14, r12
  cmp r14, r13
  cmp r14, r14
  cmp r14, r15
  cmp r15, rax
  cmp r15, rbx
  cmp r15, rcx
  cmp r15, rdx
  cmp r15, rdi
  cmp r15, rsi
  cmp r15, rbp
  cmp r15, rsp
  cmp r15, r8
  cmp r15, r9
  cmp r15, r10
  cmp r15, r11
  cmp r15, r12
  cmp r15, r13
  cmp r15, r14
  cmp r15, r15


; cmp m64,r64

  cmp qword [mem64], rax
  cmp qword [mem64], rbx
  cmp qword [mem64], rcx
  cmp qword [mem64], rdx
  cmp qword [mem64], rdi
  cmp qword [mem64], rsi
  cmp qword [mem64], rbp
  cmp qword [mem64], rsp
  cmp qword [mem64], r8
  cmp qword [mem64], r9
  cmp qword [mem64], r10
  cmp qword [mem64], r11
  cmp qword [mem64], r12
  cmp qword [mem64], r13
  cmp qword [mem64], r14
  cmp qword [mem64], r15


; cmp r64,m64

  cmp rax, qword [mem64]
  cmp rbx, qword [mem64]
  cmp rcx, qword [mem64]
  cmp rdx, qword [mem64]
  cmp rdi, qword [mem64]
  cmp rsi, qword [mem64]
  cmp rbp, qword [mem64]
  cmp rsp, qword [mem64]
  cmp r8, qword [mem64]
  cmp r9, qword [mem64]
  cmp r10, qword [mem64]
  cmp r11, qword [mem64]
  cmp r12, qword [mem64]
  cmp r13, qword [mem64]
  cmp r14, qword [mem64]
  cmp r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
