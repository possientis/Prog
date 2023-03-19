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

; add r8,r8

  add al, al
  add al, bl
  add al, cl
  add al, dl
  add al, dil
  add al, sil
  add al, bpl
  add al, spl
  add al, r8b
  add al, r9b
  add al, r10b
  add al, r11b
  add al, r12b
  add al, r13b
  add al, r14b
  add al, r15b
  add bl, al
  add bl, bl
  add bl, cl
  add bl, dl
  add bl, dil
  add bl, sil
  add bl, bpl
  add bl, spl
  add bl, r8b
  add bl, r9b
  add bl, r10b
  add bl, r11b
  add bl, r12b
  add bl, r13b
  add bl, r14b
  add bl, r15b
  add cl, al
  add cl, bl
  add cl, cl
  add cl, dl
  add cl, dil
  add cl, sil
  add cl, bpl
  add cl, spl
  add cl, r8b
  add cl, r9b
  add cl, r10b
  add cl, r11b
  add cl, r12b
  add cl, r13b
  add cl, r14b
  add cl, r15b
  add dl, al
  add dl, bl
  add dl, cl
  add dl, dl
  add dl, dil
  add dl, sil
  add dl, bpl
  add dl, spl
  add dl, r8b
  add dl, r9b
  add dl, r10b
  add dl, r11b
  add dl, r12b
  add dl, r13b
  add dl, r14b
  add dl, r15b
  add dil, al
  add dil, bl
  add dil, cl
  add dil, dl
  add dil, dil
  add dil, sil
  add dil, bpl
  add dil, spl
  add dil, r8b
  add dil, r9b
  add dil, r10b
  add dil, r11b
  add dil, r12b
  add dil, r13b
  add dil, r14b
  add dil, r15b
  add sil, al
  add sil, bl
  add sil, cl
  add sil, dl
  add sil, dil
  add sil, sil
  add sil, bpl
  add sil, spl
  add sil, r8b
  add sil, r9b
  add sil, r10b
  add sil, r11b
  add sil, r12b
  add sil, r13b
  add sil, r14b
  add sil, r15b
  add bpl, al
  add bpl, bl
  add bpl, cl
  add bpl, dl
  add bpl, dil
  add bpl, sil
  add bpl, bpl
  add bpl, spl
  add bpl, r8b
  add bpl, r9b
  add bpl, r10b
  add bpl, r11b
  add bpl, r12b
  add bpl, r13b
  add bpl, r14b
  add bpl, r15b
  add spl, al
  add spl, bl
  add spl, cl
  add spl, dl
  add spl, dil
  add spl, sil
  add spl, bpl
  add spl, spl
  add spl, r8b
  add spl, r9b
  add spl, r10b
  add spl, r11b
  add spl, r12b
  add spl, r13b
  add spl, r14b
  add spl, r15b
  add r8b, al
  add r8b, bl
  add r8b, cl
  add r8b, dl
  add r8b, dil
  add r8b, sil
  add r8b, bpl
  add r8b, spl
  add r8b, r8b
  add r8b, r9b
  add r8b, r10b
  add r8b, r11b
  add r8b, r12b
  add r8b, r13b
  add r8b, r14b
  add r8b, r15b
  add r9b, al
  add r9b, bl
  add r9b, cl
  add r9b, dl
  add r9b, dil
  add r9b, sil
  add r9b, bpl
  add r9b, spl
  add r9b, r8b
  add r9b, r9b
  add r9b, r10b
  add r9b, r11b
  add r9b, r12b
  add r9b, r13b
  add r9b, r14b
  add r9b, r15b
  add r10b, al
  add r10b, bl
  add r10b, cl
  add r10b, dl
  add r10b, dil
  add r10b, sil
  add r10b, bpl
  add r10b, spl
  add r10b, r8b
  add r10b, r9b
  add r10b, r10b
  add r10b, r11b
  add r10b, r12b
  add r10b, r13b
  add r10b, r14b
  add r10b, r15b
  add r11b, al
  add r11b, bl
  add r11b, cl
  add r11b, dl
  add r11b, dil
  add r11b, sil
  add r11b, bpl
  add r11b, spl
  add r11b, r8b
  add r11b, r9b
  add r11b, r10b
  add r11b, r11b
  add r11b, r12b
  add r11b, r13b
  add r11b, r14b
  add r11b, r15b
  add r12b, al
  add r12b, bl
  add r12b, cl
  add r12b, dl
  add r12b, dil
  add r12b, sil
  add r12b, bpl
  add r12b, spl
  add r12b, r8b
  add r12b, r9b
  add r12b, r10b
  add r12b, r11b
  add r12b, r12b
  add r12b, r13b
  add r12b, r14b
  add r12b, r15b
  add r13b, al
  add r13b, bl
  add r13b, cl
  add r13b, dl
  add r13b, dil
  add r13b, sil
  add r13b, bpl
  add r13b, spl
  add r13b, r8b
  add r13b, r9b
  add r13b, r10b
  add r13b, r11b
  add r13b, r12b
  add r13b, r13b
  add r13b, r14b
  add r13b, r15b
  add r14b, al
  add r14b, bl
  add r14b, cl
  add r14b, dl
  add r14b, dil
  add r14b, sil
  add r14b, bpl
  add r14b, spl
  add r14b, r8b
  add r14b, r9b
  add r14b, r10b
  add r14b, r11b
  add r14b, r12b
  add r14b, r13b
  add r14b, r14b
  add r14b, r15b
  add r15b, al
  add r15b, bl
  add r15b, cl
  add r15b, dl
  add r15b, dil
  add r15b, sil
  add r15b, bpl
  add r15b, spl
  add r15b, r8b
  add r15b, r9b
  add r15b, r10b
  add r15b, r11b
  add r15b, r12b
  add r15b, r13b
  add r15b, r14b
  add r15b, r15b


; add m8,r8

  add byte [mem8], al
  add byte [mem8], bl
  add byte [mem8], cl
  add byte [mem8], dl
  add byte [mem8], dil
  add byte [mem8], sil
  add byte [mem8], bpl
  add byte [mem8], spl
  add byte [mem8], r8b
  add byte [mem8], r9b
  add byte [mem8], r10b
  add byte [mem8], r11b
  add byte [mem8], r12b
  add byte [mem8], r13b
  add byte [mem8], r14b
  add byte [mem8], r15b


; add r8,m8

  add al, byte [mem8]
  add bl, byte [mem8]
  add cl, byte [mem8]
  add dl, byte [mem8]
  add dil, byte [mem8]
  add sil, byte [mem8]
  add bpl, byte [mem8]
  add spl, byte [mem8]
  add r8b, byte [mem8]
  add r9b, byte [mem8]
  add r10b, byte [mem8]
  add r11b, byte [mem8]
  add r12b, byte [mem8]
  add r13b, byte [mem8]
  add r14b, byte [mem8]
  add r15b, byte [mem8]


; add r8,i8

  add al, imm8
  add bl, imm8
  add cl, imm8
  add dl, imm8
  add dil, imm8
  add sil, imm8
  add bpl, imm8
  add spl, imm8
  add r8b, imm8
  add r9b, imm8
  add r10b, imm8
  add r11b, imm8
  add r12b, imm8
  add r13b, imm8
  add r14b, imm8
  add r15b, imm8


; add m8,i8

  add byte [mem8], imm8


; add r16,r16

  add ax, ax
  add ax, bx
  add ax, cx
  add ax, dx
  add ax, di
  add ax, si
  add ax, bp
  add ax, sp
  add ax, r8w
  add ax, r9w
  add ax, r10w
  add ax, r11w
  add ax, r12w
  add ax, r13w
  add ax, r14w
  add ax, r15w
  add bx, ax
  add bx, bx
  add bx, cx
  add bx, dx
  add bx, di
  add bx, si
  add bx, bp
  add bx, sp
  add bx, r8w
  add bx, r9w
  add bx, r10w
  add bx, r11w
  add bx, r12w
  add bx, r13w
  add bx, r14w
  add bx, r15w
  add cx, ax
  add cx, bx
  add cx, cx
  add cx, dx
  add cx, di
  add cx, si
  add cx, bp
  add cx, sp
  add cx, r8w
  add cx, r9w
  add cx, r10w
  add cx, r11w
  add cx, r12w
  add cx, r13w
  add cx, r14w
  add cx, r15w
  add dx, ax
  add dx, bx
  add dx, cx
  add dx, dx
  add dx, di
  add dx, si
  add dx, bp
  add dx, sp
  add dx, r8w
  add dx, r9w
  add dx, r10w
  add dx, r11w
  add dx, r12w
  add dx, r13w
  add dx, r14w
  add dx, r15w
  add di, ax
  add di, bx
  add di, cx
  add di, dx
  add di, di
  add di, si
  add di, bp
  add di, sp
  add di, r8w
  add di, r9w
  add di, r10w
  add di, r11w
  add di, r12w
  add di, r13w
  add di, r14w
  add di, r15w
  add si, ax
  add si, bx
  add si, cx
  add si, dx
  add si, di
  add si, si
  add si, bp
  add si, sp
  add si, r8w
  add si, r9w
  add si, r10w
  add si, r11w
  add si, r12w
  add si, r13w
  add si, r14w
  add si, r15w
  add bp, ax
  add bp, bx
  add bp, cx
  add bp, dx
  add bp, di
  add bp, si
  add bp, bp
  add bp, sp
  add bp, r8w
  add bp, r9w
  add bp, r10w
  add bp, r11w
  add bp, r12w
  add bp, r13w
  add bp, r14w
  add bp, r15w
  add sp, ax
  add sp, bx
  add sp, cx
  add sp, dx
  add sp, di
  add sp, si
  add sp, bp
  add sp, sp
  add sp, r8w
  add sp, r9w
  add sp, r10w
  add sp, r11w
  add sp, r12w
  add sp, r13w
  add sp, r14w
  add sp, r15w
  add r8w, ax
  add r8w, bx
  add r8w, cx
  add r8w, dx
  add r8w, di
  add r8w, si
  add r8w, bp
  add r8w, sp
  add r8w, r8w
  add r8w, r9w
  add r8w, r10w
  add r8w, r11w
  add r8w, r12w
  add r8w, r13w
  add r8w, r14w
  add r8w, r15w
  add r9w, ax
  add r9w, bx
  add r9w, cx
  add r9w, dx
  add r9w, di
  add r9w, si
  add r9w, bp
  add r9w, sp
  add r9w, r8w
  add r9w, r9w
  add r9w, r10w
  add r9w, r11w
  add r9w, r12w
  add r9w, r13w
  add r9w, r14w
  add r9w, r15w
  add r10w, ax
  add r10w, bx
  add r10w, cx
  add r10w, dx
  add r10w, di
  add r10w, si
  add r10w, bp
  add r10w, sp
  add r10w, r8w
  add r10w, r9w
  add r10w, r10w
  add r10w, r11w
  add r10w, r12w
  add r10w, r13w
  add r10w, r14w
  add r10w, r15w
  add r11w, ax
  add r11w, bx
  add r11w, cx
  add r11w, dx
  add r11w, di
  add r11w, si
  add r11w, bp
  add r11w, sp
  add r11w, r8w
  add r11w, r9w
  add r11w, r10w
  add r11w, r11w
  add r11w, r12w
  add r11w, r13w
  add r11w, r14w
  add r11w, r15w
  add r12w, ax
  add r12w, bx
  add r12w, cx
  add r12w, dx
  add r12w, di
  add r12w, si
  add r12w, bp
  add r12w, sp
  add r12w, r8w
  add r12w, r9w
  add r12w, r10w
  add r12w, r11w
  add r12w, r12w
  add r12w, r13w
  add r12w, r14w
  add r12w, r15w
  add r13w, ax
  add r13w, bx
  add r13w, cx
  add r13w, dx
  add r13w, di
  add r13w, si
  add r13w, bp
  add r13w, sp
  add r13w, r8w
  add r13w, r9w
  add r13w, r10w
  add r13w, r11w
  add r13w, r12w
  add r13w, r13w
  add r13w, r14w
  add r13w, r15w
  add r14w, ax
  add r14w, bx
  add r14w, cx
  add r14w, dx
  add r14w, di
  add r14w, si
  add r14w, bp
  add r14w, sp
  add r14w, r8w
  add r14w, r9w
  add r14w, r10w
  add r14w, r11w
  add r14w, r12w
  add r14w, r13w
  add r14w, r14w
  add r14w, r15w
  add r15w, ax
  add r15w, bx
  add r15w, cx
  add r15w, dx
  add r15w, di
  add r15w, si
  add r15w, bp
  add r15w, sp
  add r15w, r8w
  add r15w, r9w
  add r15w, r10w
  add r15w, r11w
  add r15w, r12w
  add r15w, r13w
  add r15w, r14w
  add r15w, r15w


; add m16,r16

  add word [mem16], ax
  add word [mem16], bx
  add word [mem16], cx
  add word [mem16], dx
  add word [mem16], di
  add word [mem16], si
  add word [mem16], bp
  add word [mem16], sp
  add word [mem16], r8w
  add word [mem16], r9w
  add word [mem16], r10w
  add word [mem16], r11w
  add word [mem16], r12w
  add word [mem16], r13w
  add word [mem16], r14w
  add word [mem16], r15w


; add r16,m16

  add ax, word [mem16]
  add bx, word [mem16]
  add cx, word [mem16]
  add dx, word [mem16]
  add di, word [mem16]
  add si, word [mem16]
  add bp, word [mem16]
  add sp, word [mem16]
  add r8w, word [mem16]
  add r9w, word [mem16]
  add r10w, word [mem16]
  add r11w, word [mem16]
  add r12w, word [mem16]
  add r13w, word [mem16]
  add r14w, word [mem16]
  add r15w, word [mem16]


; add r16,i16

  add ax, imm16
  add bx, imm16
  add cx, imm16
  add dx, imm16
  add di, imm16
  add si, imm16
  add bp, imm16
  add sp, imm16
  add r8w, imm16
  add r9w, imm16
  add r10w, imm16
  add r11w, imm16
  add r12w, imm16
  add r13w, imm16
  add r14w, imm16
  add r15w, imm16


; add m16,i16

  add word [mem16], imm16


; add r32,r32

  add eax, eax
  add eax, ebx
  add eax, ecx
  add eax, edx
  add eax, edi
  add eax, esi
  add eax, ebp
  add eax, esp
  add eax, r8d
  add eax, r9d
  add eax, r10d
  add eax, r11d
  add eax, r12d
  add eax, r13d
  add eax, r14d
  add eax, r15d
  add ebx, eax
  add ebx, ebx
  add ebx, ecx
  add ebx, edx
  add ebx, edi
  add ebx, esi
  add ebx, ebp
  add ebx, esp
  add ebx, r8d
  add ebx, r9d
  add ebx, r10d
  add ebx, r11d
  add ebx, r12d
  add ebx, r13d
  add ebx, r14d
  add ebx, r15d
  add ecx, eax
  add ecx, ebx
  add ecx, ecx
  add ecx, edx
  add ecx, edi
  add ecx, esi
  add ecx, ebp
  add ecx, esp
  add ecx, r8d
  add ecx, r9d
  add ecx, r10d
  add ecx, r11d
  add ecx, r12d
  add ecx, r13d
  add ecx, r14d
  add ecx, r15d
  add edx, eax
  add edx, ebx
  add edx, ecx
  add edx, edx
  add edx, edi
  add edx, esi
  add edx, ebp
  add edx, esp
  add edx, r8d
  add edx, r9d
  add edx, r10d
  add edx, r11d
  add edx, r12d
  add edx, r13d
  add edx, r14d
  add edx, r15d
  add edi, eax
  add edi, ebx
  add edi, ecx
  add edi, edx
  add edi, edi
  add edi, esi
  add edi, ebp
  add edi, esp
  add edi, r8d
  add edi, r9d
  add edi, r10d
  add edi, r11d
  add edi, r12d
  add edi, r13d
  add edi, r14d
  add edi, r15d
  add esi, eax
  add esi, ebx
  add esi, ecx
  add esi, edx
  add esi, edi
  add esi, esi
  add esi, ebp
  add esi, esp
  add esi, r8d
  add esi, r9d
  add esi, r10d
  add esi, r11d
  add esi, r12d
  add esi, r13d
  add esi, r14d
  add esi, r15d
  add ebp, eax
  add ebp, ebx
  add ebp, ecx
  add ebp, edx
  add ebp, edi
  add ebp, esi
  add ebp, ebp
  add ebp, esp
  add ebp, r8d
  add ebp, r9d
  add ebp, r10d
  add ebp, r11d
  add ebp, r12d
  add ebp, r13d
  add ebp, r14d
  add ebp, r15d
  add esp, eax
  add esp, ebx
  add esp, ecx
  add esp, edx
  add esp, edi
  add esp, esi
  add esp, ebp
  add esp, esp
  add esp, r8d
  add esp, r9d
  add esp, r10d
  add esp, r11d
  add esp, r12d
  add esp, r13d
  add esp, r14d
  add esp, r15d
  add r8d, eax
  add r8d, ebx
  add r8d, ecx
  add r8d, edx
  add r8d, edi
  add r8d, esi
  add r8d, ebp
  add r8d, esp
  add r8d, r8d
  add r8d, r9d
  add r8d, r10d
  add r8d, r11d
  add r8d, r12d
  add r8d, r13d
  add r8d, r14d
  add r8d, r15d
  add r9d, eax
  add r9d, ebx
  add r9d, ecx
  add r9d, edx
  add r9d, edi
  add r9d, esi
  add r9d, ebp
  add r9d, esp
  add r9d, r8d
  add r9d, r9d
  add r9d, r10d
  add r9d, r11d
  add r9d, r12d
  add r9d, r13d
  add r9d, r14d
  add r9d, r15d
  add r10d, eax
  add r10d, ebx
  add r10d, ecx
  add r10d, edx
  add r10d, edi
  add r10d, esi
  add r10d, ebp
  add r10d, esp
  add r10d, r8d
  add r10d, r9d
  add r10d, r10d
  add r10d, r11d
  add r10d, r12d
  add r10d, r13d
  add r10d, r14d
  add r10d, r15d
  add r11d, eax
  add r11d, ebx
  add r11d, ecx
  add r11d, edx
  add r11d, edi
  add r11d, esi
  add r11d, ebp
  add r11d, esp
  add r11d, r8d
  add r11d, r9d
  add r11d, r10d
  add r11d, r11d
  add r11d, r12d
  add r11d, r13d
  add r11d, r14d
  add r11d, r15d
  add r12d, eax
  add r12d, ebx
  add r12d, ecx
  add r12d, edx
  add r12d, edi
  add r12d, esi
  add r12d, ebp
  add r12d, esp
  add r12d, r8d
  add r12d, r9d
  add r12d, r10d
  add r12d, r11d
  add r12d, r12d
  add r12d, r13d
  add r12d, r14d
  add r12d, r15d
  add r13d, eax
  add r13d, ebx
  add r13d, ecx
  add r13d, edx
  add r13d, edi
  add r13d, esi
  add r13d, ebp
  add r13d, esp
  add r13d, r8d
  add r13d, r9d
  add r13d, r10d
  add r13d, r11d
  add r13d, r12d
  add r13d, r13d
  add r13d, r14d
  add r13d, r15d
  add r14d, eax
  add r14d, ebx
  add r14d, ecx
  add r14d, edx
  add r14d, edi
  add r14d, esi
  add r14d, ebp
  add r14d, esp
  add r14d, r8d
  add r14d, r9d
  add r14d, r10d
  add r14d, r11d
  add r14d, r12d
  add r14d, r13d
  add r14d, r14d
  add r14d, r15d
  add r15d, eax
  add r15d, ebx
  add r15d, ecx
  add r15d, edx
  add r15d, edi
  add r15d, esi
  add r15d, ebp
  add r15d, esp
  add r15d, r8d
  add r15d, r9d
  add r15d, r10d
  add r15d, r11d
  add r15d, r12d
  add r15d, r13d
  add r15d, r14d
  add r15d, r15d


; add m32,r32

  add dword [mem32], eax
  add dword [mem32], ebx
  add dword [mem32], ecx
  add dword [mem32], edx
  add dword [mem32], edi
  add dword [mem32], esi
  add dword [mem32], ebp
  add dword [mem32], esp
  add dword [mem32], r8d
  add dword [mem32], r9d
  add dword [mem32], r10d
  add dword [mem32], r11d
  add dword [mem32], r12d
  add dword [mem32], r13d
  add dword [mem32], r14d
  add dword [mem32], r15d


; add r32,m32

  add eax, dword [mem32]
  add ebx, dword [mem32]
  add ecx, dword [mem32]
  add edx, dword [mem32]
  add edi, dword [mem32]
  add esi, dword [mem32]
  add ebp, dword [mem32]
  add esp, dword [mem32]
  add r8d, dword [mem32]
  add r9d, dword [mem32]
  add r10d, dword [mem32]
  add r11d, dword [mem32]
  add r12d, dword [mem32]
  add r13d, dword [mem32]
  add r14d, dword [mem32]
  add r15d, dword [mem32]


; add r32,i32

  add eax, imm32
  add ebx, imm32
  add ecx, imm32
  add edx, imm32
  add edi, imm32
  add esi, imm32
  add ebp, imm32
  add esp, imm32
  add r8d, imm32
  add r9d, imm32
  add r10d, imm32
  add r11d, imm32
  add r12d, imm32
  add r13d, imm32
  add r14d, imm32
  add r15d, imm32


; add m32,i32

  add dword [mem32], imm32


; add r64,r64

  add rax, rax
  add rax, rbx
  add rax, rcx
  add rax, rdx
  add rax, rdi
  add rax, rsi
  add rax, rbp
  add rax, rsp
  add rax, r8
  add rax, r9
  add rax, r10
  add rax, r11
  add rax, r12
  add rax, r13
  add rax, r14
  add rax, r15
  add rbx, rax
  add rbx, rbx
  add rbx, rcx
  add rbx, rdx
  add rbx, rdi
  add rbx, rsi
  add rbx, rbp
  add rbx, rsp
  add rbx, r8
  add rbx, r9
  add rbx, r10
  add rbx, r11
  add rbx, r12
  add rbx, r13
  add rbx, r14
  add rbx, r15
  add rcx, rax
  add rcx, rbx
  add rcx, rcx
  add rcx, rdx
  add rcx, rdi
  add rcx, rsi
  add rcx, rbp
  add rcx, rsp
  add rcx, r8
  add rcx, r9
  add rcx, r10
  add rcx, r11
  add rcx, r12
  add rcx, r13
  add rcx, r14
  add rcx, r15
  add rdx, rax
  add rdx, rbx
  add rdx, rcx
  add rdx, rdx
  add rdx, rdi
  add rdx, rsi
  add rdx, rbp
  add rdx, rsp
  add rdx, r8
  add rdx, r9
  add rdx, r10
  add rdx, r11
  add rdx, r12
  add rdx, r13
  add rdx, r14
  add rdx, r15
  add rdi, rax
  add rdi, rbx
  add rdi, rcx
  add rdi, rdx
  add rdi, rdi
  add rdi, rsi
  add rdi, rbp
  add rdi, rsp
  add rdi, r8
  add rdi, r9
  add rdi, r10
  add rdi, r11
  add rdi, r12
  add rdi, r13
  add rdi, r14
  add rdi, r15
  add rsi, rax
  add rsi, rbx
  add rsi, rcx
  add rsi, rdx
  add rsi, rdi
  add rsi, rsi
  add rsi, rbp
  add rsi, rsp
  add rsi, r8
  add rsi, r9
  add rsi, r10
  add rsi, r11
  add rsi, r12
  add rsi, r13
  add rsi, r14
  add rsi, r15
  add rbp, rax
  add rbp, rbx
  add rbp, rcx
  add rbp, rdx
  add rbp, rdi
  add rbp, rsi
  add rbp, rbp
  add rbp, rsp
  add rbp, r8
  add rbp, r9
  add rbp, r10
  add rbp, r11
  add rbp, r12
  add rbp, r13
  add rbp, r14
  add rbp, r15
  add rsp, rax
  add rsp, rbx
  add rsp, rcx
  add rsp, rdx
  add rsp, rdi
  add rsp, rsi
  add rsp, rbp
  add rsp, rsp
  add rsp, r8
  add rsp, r9
  add rsp, r10
  add rsp, r11
  add rsp, r12
  add rsp, r13
  add rsp, r14
  add rsp, r15
  add r8, rax
  add r8, rbx
  add r8, rcx
  add r8, rdx
  add r8, rdi
  add r8, rsi
  add r8, rbp
  add r8, rsp
  add r8, r8
  add r8, r9
  add r8, r10
  add r8, r11
  add r8, r12
  add r8, r13
  add r8, r14
  add r8, r15
  add r9, rax
  add r9, rbx
  add r9, rcx
  add r9, rdx
  add r9, rdi
  add r9, rsi
  add r9, rbp
  add r9, rsp
  add r9, r8
  add r9, r9
  add r9, r10
  add r9, r11
  add r9, r12
  add r9, r13
  add r9, r14
  add r9, r15
  add r10, rax
  add r10, rbx
  add r10, rcx
  add r10, rdx
  add r10, rdi
  add r10, rsi
  add r10, rbp
  add r10, rsp
  add r10, r8
  add r10, r9
  add r10, r10
  add r10, r11
  add r10, r12
  add r10, r13
  add r10, r14
  add r10, r15
  add r11, rax
  add r11, rbx
  add r11, rcx
  add r11, rdx
  add r11, rdi
  add r11, rsi
  add r11, rbp
  add r11, rsp
  add r11, r8
  add r11, r9
  add r11, r10
  add r11, r11
  add r11, r12
  add r11, r13
  add r11, r14
  add r11, r15
  add r12, rax
  add r12, rbx
  add r12, rcx
  add r12, rdx
  add r12, rdi
  add r12, rsi
  add r12, rbp
  add r12, rsp
  add r12, r8
  add r12, r9
  add r12, r10
  add r12, r11
  add r12, r12
  add r12, r13
  add r12, r14
  add r12, r15
  add r13, rax
  add r13, rbx
  add r13, rcx
  add r13, rdx
  add r13, rdi
  add r13, rsi
  add r13, rbp
  add r13, rsp
  add r13, r8
  add r13, r9
  add r13, r10
  add r13, r11
  add r13, r12
  add r13, r13
  add r13, r14
  add r13, r15
  add r14, rax
  add r14, rbx
  add r14, rcx
  add r14, rdx
  add r14, rdi
  add r14, rsi
  add r14, rbp
  add r14, rsp
  add r14, r8
  add r14, r9
  add r14, r10
  add r14, r11
  add r14, r12
  add r14, r13
  add r14, r14
  add r14, r15
  add r15, rax
  add r15, rbx
  add r15, rcx
  add r15, rdx
  add r15, rdi
  add r15, rsi
  add r15, rbp
  add r15, rsp
  add r15, r8
  add r15, r9
  add r15, r10
  add r15, r11
  add r15, r12
  add r15, r13
  add r15, r14
  add r15, r15


; add m64,r64

  add qword [mem64], rax
  add qword [mem64], rbx
  add qword [mem64], rcx
  add qword [mem64], rdx
  add qword [mem64], rdi
  add qword [mem64], rsi
  add qword [mem64], rbp
  add qword [mem64], rsp
  add qword [mem64], r8
  add qword [mem64], r9
  add qword [mem64], r10
  add qword [mem64], r11
  add qword [mem64], r12
  add qword [mem64], r13
  add qword [mem64], r14
  add qword [mem64], r15


; add r64,m64

  add rax, qword [mem64]
  add rbx, qword [mem64]
  add rcx, qword [mem64]
  add rdx, qword [mem64]
  add rdi, qword [mem64]
  add rsi, qword [mem64]
  add rbp, qword [mem64]
  add rsp, qword [mem64]
  add r8, qword [mem64]
  add r9, qword [mem64]
  add r10, qword [mem64]
  add r11, qword [mem64]
  add r12, qword [mem64]
  add r13, qword [mem64]
  add r14, qword [mem64]
  add r15, qword [mem64]

  mov rax, 60
  mov rdi, 0
  syscall
