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

; mov r8,r8

  mov al, al
  mov al, bl
  mov al, cl
  mov al, dl
  mov al, dil
  mov al, sil
  mov al, bpl
  mov al, spl
  mov al, r8b
  mov al, r9b
  mov al, r10b
  mov al, r11b
  mov al, r12b
  mov al, r13b
  mov al, r14b
  mov al, r15b
  mov bl, al
  mov bl, bl
  mov bl, cl
  mov bl, dl
  mov bl, dil
  mov bl, sil
  mov bl, bpl
  mov bl, spl
  mov bl, r8b
  mov bl, r9b
  mov bl, r10b
  mov bl, r11b
  mov bl, r12b
  mov bl, r13b
  mov bl, r14b
  mov bl, r15b
  mov cl, al
  mov cl, bl
  mov cl, cl
  mov cl, dl
  mov cl, dil
  mov cl, sil
  mov cl, bpl
  mov cl, spl
  mov cl, r8b
  mov cl, r9b
  mov cl, r10b
  mov cl, r11b
  mov cl, r12b
  mov cl, r13b
  mov cl, r14b
  mov cl, r15b
  mov dl, al
  mov dl, bl
  mov dl, cl
  mov dl, dl
  mov dl, dil
  mov dl, sil
  mov dl, bpl
  mov dl, spl
  mov dl, r8b
  mov dl, r9b
  mov dl, r10b
  mov dl, r11b
  mov dl, r12b
  mov dl, r13b
  mov dl, r14b
  mov dl, r15b
  mov dil, al
  mov dil, bl
  mov dil, cl
  mov dil, dl
  mov dil, dil
  mov dil, sil
  mov dil, bpl
  mov dil, spl
  mov dil, r8b
  mov dil, r9b
  mov dil, r10b
  mov dil, r11b
  mov dil, r12b
  mov dil, r13b
  mov dil, r14b
  mov dil, r15b
  mov sil, al
  mov sil, bl
  mov sil, cl
  mov sil, dl
  mov sil, dil
  mov sil, sil
  mov sil, bpl
  mov sil, spl
  mov sil, r8b
  mov sil, r9b
  mov sil, r10b
  mov sil, r11b
  mov sil, r12b
  mov sil, r13b
  mov sil, r14b
  mov sil, r15b
  mov bpl, al
  mov bpl, bl
  mov bpl, cl
  mov bpl, dl
  mov bpl, dil
  mov bpl, sil
  mov bpl, bpl
  mov bpl, spl
  mov bpl, r8b
  mov bpl, r9b
  mov bpl, r10b
  mov bpl, r11b
  mov bpl, r12b
  mov bpl, r13b
  mov bpl, r14b
  mov bpl, r15b
  mov spl, al
  mov spl, bl
  mov spl, cl
  mov spl, dl
  mov spl, dil
  mov spl, sil
  mov spl, bpl
  mov spl, spl
  mov spl, r8b
  mov spl, r9b
  mov spl, r10b
  mov spl, r11b
  mov spl, r12b
  mov spl, r13b
  mov spl, r14b
  mov spl, r15b
  mov r8b, al
  mov r8b, bl
  mov r8b, cl
  mov r8b, dl
  mov r8b, dil
  mov r8b, sil
  mov r8b, bpl
  mov r8b, spl
  mov r8b, r8b
  mov r8b, r9b
  mov r8b, r10b
  mov r8b, r11b
  mov r8b, r12b
  mov r8b, r13b
  mov r8b, r14b
  mov r8b, r15b
  mov r9b, al
  mov r9b, bl
  mov r9b, cl
  mov r9b, dl
  mov r9b, dil
  mov r9b, sil
  mov r9b, bpl
  mov r9b, spl
  mov r9b, r8b
  mov r9b, r9b
  mov r9b, r10b
  mov r9b, r11b
  mov r9b, r12b
  mov r9b, r13b
  mov r9b, r14b
  mov r9b, r15b
  mov r10b, al
  mov r10b, bl
  mov r10b, cl
  mov r10b, dl
  mov r10b, dil
  mov r10b, sil
  mov r10b, bpl
  mov r10b, spl
  mov r10b, r8b
  mov r10b, r9b
  mov r10b, r10b
  mov r10b, r11b
  mov r10b, r12b
  mov r10b, r13b
  mov r10b, r14b
  mov r10b, r15b
  mov r11b, al
  mov r11b, bl
  mov r11b, cl
  mov r11b, dl
  mov r11b, dil
  mov r11b, sil
  mov r11b, bpl
  mov r11b, spl
  mov r11b, r8b
  mov r11b, r9b
  mov r11b, r10b
  mov r11b, r11b
  mov r11b, r12b
  mov r11b, r13b
  mov r11b, r14b
  mov r11b, r15b
  mov r12b, al
  mov r12b, bl
  mov r12b, cl
  mov r12b, dl
  mov r12b, dil
  mov r12b, sil
  mov r12b, bpl
  mov r12b, spl
  mov r12b, r8b
  mov r12b, r9b
  mov r12b, r10b
  mov r12b, r11b
  mov r12b, r12b
  mov r12b, r13b
  mov r12b, r14b
  mov r12b, r15b
  mov r13b, al
  mov r13b, bl
  mov r13b, cl
  mov r13b, dl
  mov r13b, dil
  mov r13b, sil
  mov r13b, bpl
  mov r13b, spl
  mov r13b, r8b
  mov r13b, r9b
  mov r13b, r10b
  mov r13b, r11b
  mov r13b, r12b
  mov r13b, r13b
  mov r13b, r14b
  mov r13b, r15b
  mov r14b, al
  mov r14b, bl
  mov r14b, cl
  mov r14b, dl
  mov r14b, dil
  mov r14b, sil
  mov r14b, bpl
  mov r14b, spl
  mov r14b, r8b
  mov r14b, r9b
  mov r14b, r10b
  mov r14b, r11b
  mov r14b, r12b
  mov r14b, r13b
  mov r14b, r14b
  mov r14b, r15b
  mov r15b, al
  mov r15b, bl
  mov r15b, cl
  mov r15b, dl
  mov r15b, dil
  mov r15b, sil
  mov r15b, bpl
  mov r15b, spl
  mov r15b, r8b
  mov r15b, r9b
  mov r15b, r10b
  mov r15b, r11b
  mov r15b, r12b
  mov r15b, r13b
  mov r15b, r14b
  mov r15b, r15b


; mov m8,r8

  mov byte [mem8], al
  mov byte [mem8], bl
  mov byte [mem8], cl
  mov byte [mem8], dl
  mov byte [mem8], dil
  mov byte [mem8], sil
  mov byte [mem8], bpl
  mov byte [mem8], spl
  mov byte [mem8], r8b
  mov byte [mem8], r9b
  mov byte [mem8], r10b
  mov byte [mem8], r11b
  mov byte [mem8], r12b
  mov byte [mem8], r13b
  mov byte [mem8], r14b
  mov byte [mem8], r15b


; mov r8,m8

  mov al, byte [mem8]
  mov bl, byte [mem8]
  mov cl, byte [mem8]
  mov dl, byte [mem8]
  mov dil, byte [mem8]
  mov sil, byte [mem8]
  mov bpl, byte [mem8]
  mov spl, byte [mem8]
  mov r8b, byte [mem8]
  mov r9b, byte [mem8]
  mov r10b, byte [mem8]
  mov r11b, byte [mem8]
  mov r12b, byte [mem8]
  mov r13b, byte [mem8]
  mov r14b, byte [mem8]
  mov r15b, byte [mem8]


; mov r8,i8

  mov al, imm8
  mov bl, imm8
  mov cl, imm8
  mov dl, imm8
  mov dil, imm8
  mov sil, imm8
  mov bpl, imm8
  mov spl, imm8
  mov r8b, imm8
  mov r9b, imm8
  mov r10b, imm8
  mov r11b, imm8
  mov r12b, imm8
  mov r13b, imm8
  mov r14b, imm8
  mov r15b, imm8


; mov m8,i8

  mov byte [mem8], imm8


; mov r16,r16

  mov ax, ax
  mov ax, bx
  mov ax, cx
  mov ax, dx
  mov ax, di
  mov ax, si
  mov ax, bp
  mov ax, sp
  mov ax, r8w
  mov ax, r9w
  mov ax, r10w
  mov ax, r11w
  mov ax, r12w
  mov ax, r13w
  mov ax, r14w
  mov ax, r15w
  mov bx, ax
  mov bx, bx
  mov bx, cx
  mov bx, dx
  mov bx, di
  mov bx, si
  mov bx, bp
  mov bx, sp
  mov bx, r8w
  mov bx, r9w
  mov bx, r10w
  mov bx, r11w
  mov bx, r12w
  mov bx, r13w
  mov bx, r14w
  mov bx, r15w
  mov cx, ax
  mov cx, bx
  mov cx, cx
  mov cx, dx
  mov cx, di
  mov cx, si
  mov cx, bp
  mov cx, sp
  mov cx, r8w
  mov cx, r9w
  mov cx, r10w
  mov cx, r11w
  mov cx, r12w
  mov cx, r13w
  mov cx, r14w
  mov cx, r15w
  mov dx, ax
  mov dx, bx
  mov dx, cx
  mov dx, dx
  mov dx, di
  mov dx, si
  mov dx, bp
  mov dx, sp
  mov dx, r8w
  mov dx, r9w
  mov dx, r10w
  mov dx, r11w
  mov dx, r12w
  mov dx, r13w
  mov dx, r14w
  mov dx, r15w
  mov di, ax
  mov di, bx
  mov di, cx
  mov di, dx
  mov di, di
  mov di, si
  mov di, bp
  mov di, sp
  mov di, r8w
  mov di, r9w
  mov di, r10w
  mov di, r11w
  mov di, r12w
  mov di, r13w
  mov di, r14w
  mov di, r15w
  mov si, ax
  mov si, bx
  mov si, cx
  mov si, dx
  mov si, di
  mov si, si
  mov si, bp
  mov si, sp
  mov si, r8w
  mov si, r9w
  mov si, r10w
  mov si, r11w
  mov si, r12w
  mov si, r13w
  mov si, r14w
  mov si, r15w
  mov bp, ax
  mov bp, bx
  mov bp, cx
  mov bp, dx
  mov bp, di
  mov bp, si
  mov bp, bp
  mov bp, sp
  mov bp, r8w
  mov bp, r9w
  mov bp, r10w
  mov bp, r11w
  mov bp, r12w
  mov bp, r13w
  mov bp, r14w
  mov bp, r15w
  mov sp, ax
  mov sp, bx
  mov sp, cx
  mov sp, dx
  mov sp, di
  mov sp, si
  mov sp, bp
  mov sp, sp
  mov sp, r8w
  mov sp, r9w
  mov sp, r10w
  mov sp, r11w
  mov sp, r12w
  mov sp, r13w
  mov sp, r14w
  mov sp, r15w
  mov r8w, ax
  mov r8w, bx
  mov r8w, cx
  mov r8w, dx
  mov r8w, di
  mov r8w, si
  mov r8w, bp
  mov r8w, sp
  mov r8w, r8w
  mov r8w, r9w
  mov r8w, r10w
  mov r8w, r11w
  mov r8w, r12w
  mov r8w, r13w
  mov r8w, r14w
  mov r8w, r15w
  mov r9w, ax
  mov r9w, bx
  mov r9w, cx
  mov r9w, dx
  mov r9w, di
  mov r9w, si
  mov r9w, bp
  mov r9w, sp
  mov r9w, r8w
  mov r9w, r9w
  mov r9w, r10w
  mov r9w, r11w
  mov r9w, r12w
  mov r9w, r13w
  mov r9w, r14w
  mov r9w, r15w
  mov r10w, ax
  mov r10w, bx
  mov r10w, cx
  mov r10w, dx
  mov r10w, di
  mov r10w, si
  mov r10w, bp
  mov r10w, sp
  mov r10w, r8w
  mov r10w, r9w
  mov r10w, r10w
  mov r10w, r11w
  mov r10w, r12w
  mov r10w, r13w
  mov r10w, r14w
  mov r10w, r15w
  mov r11w, ax
  mov r11w, bx
  mov r11w, cx
  mov r11w, dx
  mov r11w, di
  mov r11w, si
  mov r11w, bp
  mov r11w, sp
  mov r11w, r8w
  mov r11w, r9w
  mov r11w, r10w
  mov r11w, r11w
  mov r11w, r12w
  mov r11w, r13w
  mov r11w, r14w
  mov r11w, r15w
  mov r12w, ax
  mov r12w, bx
  mov r12w, cx
  mov r12w, dx
  mov r12w, di
  mov r12w, si
  mov r12w, bp
  mov r12w, sp
  mov r12w, r8w
  mov r12w, r9w
  mov r12w, r10w
  mov r12w, r11w
  mov r12w, r12w
  mov r12w, r13w
  mov r12w, r14w
  mov r12w, r15w
  mov r13w, ax
  mov r13w, bx
  mov r13w, cx
  mov r13w, dx
  mov r13w, di
  mov r13w, si
  mov r13w, bp
  mov r13w, sp
  mov r13w, r8w
  mov r13w, r9w
  mov r13w, r10w
  mov r13w, r11w
  mov r13w, r12w
  mov r13w, r13w
  mov r13w, r14w
  mov r13w, r15w
  mov r14w, ax
  mov r14w, bx
  mov r14w, cx
  mov r14w, dx
  mov r14w, di
  mov r14w, si
  mov r14w, bp
  mov r14w, sp
  mov r14w, r8w
  mov r14w, r9w
  mov r14w, r10w
  mov r14w, r11w
  mov r14w, r12w
  mov r14w, r13w
  mov r14w, r14w
  mov r14w, r15w
  mov r15w, ax
  mov r15w, bx
  mov r15w, cx
  mov r15w, dx
  mov r15w, di
  mov r15w, si
  mov r15w, bp
  mov r15w, sp
  mov r15w, r8w
  mov r15w, r9w
  mov r15w, r10w
  mov r15w, r11w
  mov r15w, r12w
  mov r15w, r13w
  mov r15w, r14w
  mov r15w, r15w


; mov m16,r16

  mov word [mem16], ax
  mov word [mem16], bx
  mov word [mem16], cx
  mov word [mem16], dx
  mov word [mem16], di
  mov word [mem16], si
  mov word [mem16], bp
  mov word [mem16], sp
  mov word [mem16], r8w
  mov word [mem16], r9w
  mov word [mem16], r10w
  mov word [mem16], r11w
  mov word [mem16], r12w
  mov word [mem16], r13w
  mov word [mem16], r14w
  mov word [mem16], r15w


; mov r16,m16

  mov ax, word [mem16]
  mov bx, word [mem16]
  mov cx, word [mem16]
  mov dx, word [mem16]
  mov di, word [mem16]
  mov si, word [mem16]
  mov bp, word [mem16]
  mov sp, word [mem16]
  mov r8w, word [mem16]
  mov r9w, word [mem16]
  mov r10w, word [mem16]
  mov r11w, word [mem16]
  mov r12w, word [mem16]
  mov r13w, word [mem16]
  mov r14w, word [mem16]
  mov r15w, word [mem16]


; mov r16,i16

  mov ax, imm16
  mov bx, imm16
  mov cx, imm16
  mov dx, imm16
  mov di, imm16
  mov si, imm16
  mov bp, imm16
  mov sp, imm16
  mov r8w, imm16
  mov r9w, imm16
  mov r10w, imm16
  mov r11w, imm16
  mov r12w, imm16
  mov r13w, imm16
  mov r14w, imm16
  mov r15w, imm16


; mov m16,i16

  mov word [mem16], imm16


; mov r32,r32

  mov eax, eax
  mov eax, ebx
  mov eax, ecx
  mov eax, edx
  mov eax, edi
  mov eax, esi
  mov eax, ebp
  mov eax, esp
  mov eax, r8d
  mov eax, r9d
  mov eax, r10d
  mov eax, r11d
  mov eax, r12d
  mov eax, r13d
  mov eax, r14d
  mov eax, r15d
  mov ebx, eax
  mov ebx, ebx
  mov ebx, ecx
  mov ebx, edx
  mov ebx, edi
  mov ebx, esi
  mov ebx, ebp
  mov ebx, esp
  mov ebx, r8d
  mov ebx, r9d
  mov ebx, r10d
  mov ebx, r11d
  mov ebx, r12d
  mov ebx, r13d
  mov ebx, r14d
  mov ebx, r15d
  mov ecx, eax
  mov ecx, ebx
  mov ecx, ecx
  mov ecx, edx
  mov ecx, edi
  mov ecx, esi
  mov ecx, ebp
  mov ecx, esp
  mov ecx, r8d
  mov ecx, r9d
  mov ecx, r10d
  mov ecx, r11d
  mov ecx, r12d
  mov ecx, r13d
  mov ecx, r14d
  mov ecx, r15d
  mov edx, eax
  mov edx, ebx
  mov edx, ecx
  mov edx, edx
  mov edx, edi
  mov edx, esi
  mov edx, ebp
  mov edx, esp
  mov edx, r8d
  mov edx, r9d
  mov edx, r10d
  mov edx, r11d
  mov edx, r12d
  mov edx, r13d
  mov edx, r14d
  mov edx, r15d
  mov edi, eax
  mov edi, ebx
  mov edi, ecx
  mov edi, edx
  mov edi, edi
  mov edi, esi
  mov edi, ebp
  mov edi, esp
  mov edi, r8d
  mov edi, r9d
  mov edi, r10d
  mov edi, r11d
  mov edi, r12d
  mov edi, r13d
  mov edi, r14d
  mov edi, r15d
  mov esi, eax
  mov esi, ebx
  mov esi, ecx
  mov esi, edx
  mov esi, edi
  mov esi, esi
  mov esi, ebp
  mov esi, esp
  mov esi, r8d
  mov esi, r9d
  mov esi, r10d
  mov esi, r11d
  mov esi, r12d
  mov esi, r13d
  mov esi, r14d
  mov esi, r15d
  mov ebp, eax
  mov ebp, ebx
  mov ebp, ecx
  mov ebp, edx
  mov ebp, edi
  mov ebp, esi
  mov ebp, ebp
  mov ebp, esp
  mov ebp, r8d
  mov ebp, r9d
  mov ebp, r10d
  mov ebp, r11d
  mov ebp, r12d
  mov ebp, r13d
  mov ebp, r14d
  mov ebp, r15d
  mov esp, eax
  mov esp, ebx
  mov esp, ecx
  mov esp, edx
  mov esp, edi
  mov esp, esi
  mov esp, ebp
  mov esp, esp
  mov esp, r8d
  mov esp, r9d
  mov esp, r10d
  mov esp, r11d
  mov esp, r12d
  mov esp, r13d
  mov esp, r14d
  mov esp, r15d
  mov r8d, eax
  mov r8d, ebx
  mov r8d, ecx
  mov r8d, edx
  mov r8d, edi
  mov r8d, esi
  mov r8d, ebp
  mov r8d, esp
  mov r8d, r8d
  mov r8d, r9d
  mov r8d, r10d
  mov r8d, r11d
  mov r8d, r12d
  mov r8d, r13d
  mov r8d, r14d
  mov r8d, r15d
  mov r9d, eax
  mov r9d, ebx
  mov r9d, ecx
  mov r9d, edx
  mov r9d, edi
  mov r9d, esi
  mov r9d, ebp
  mov r9d, esp
  mov r9d, r8d
  mov r9d, r9d
  mov r9d, r10d
  mov r9d, r11d
  mov r9d, r12d
  mov r9d, r13d
  mov r9d, r14d
  mov r9d, r15d
  mov r10d, eax
  mov r10d, ebx
  mov r10d, ecx
  mov r10d, edx
  mov r10d, edi
  mov r10d, esi
  mov r10d, ebp
  mov r10d, esp
  mov r10d, r8d
  mov r10d, r9d
  mov r10d, r10d
  mov r10d, r11d
  mov r10d, r12d
  mov r10d, r13d
  mov r10d, r14d
  mov r10d, r15d
  mov r11d, eax
  mov r11d, ebx
  mov r11d, ecx
  mov r11d, edx
  mov r11d, edi
  mov r11d, esi
  mov r11d, ebp
  mov r11d, esp
  mov r11d, r8d
  mov r11d, r9d
  mov r11d, r10d
  mov r11d, r11d
  mov r11d, r12d
  mov r11d, r13d
  mov r11d, r14d
  mov r11d, r15d
  mov r12d, eax
  mov r12d, ebx
  mov r12d, ecx
  mov r12d, edx
  mov r12d, edi
  mov r12d, esi
  mov r12d, ebp
  mov r12d, esp
  mov r12d, r8d
  mov r12d, r9d
  mov r12d, r10d
  mov r12d, r11d
  mov r12d, r12d
  mov r12d, r13d
  mov r12d, r14d
  mov r12d, r15d
  mov r13d, eax
  mov r13d, ebx
  mov r13d, ecx
  mov r13d, edx
  mov r13d, edi
  mov r13d, esi
  mov r13d, ebp
  mov r13d, esp
  mov r13d, r8d
  mov r13d, r9d
  mov r13d, r10d
  mov r13d, r11d
  mov r13d, r12d
  mov r13d, r13d
  mov r13d, r14d
  mov r13d, r15d
  mov r14d, eax
  mov r14d, ebx
  mov r14d, ecx
  mov r14d, edx
  mov r14d, edi
  mov r14d, esi
  mov r14d, ebp
  mov r14d, esp
  mov r14d, r8d
  mov r14d, r9d
  mov r14d, r10d
  mov r14d, r11d
  mov r14d, r12d
  mov r14d, r13d
  mov r14d, r14d
  mov r14d, r15d
  mov r15d, eax
  mov r15d, ebx
  mov r15d, ecx
  mov r15d, edx
  mov r15d, edi
  mov r15d, esi
  mov r15d, ebp
  mov r15d, esp
  mov r15d, r8d
  mov r15d, r9d
  mov r15d, r10d
  mov r15d, r11d
  mov r15d, r12d
  mov r15d, r13d
  mov r15d, r14d
  mov r15d, r15d


; mov m32,r32

  mov dword [mem32], eax
  mov dword [mem32], ebx
  mov dword [mem32], ecx
  mov dword [mem32], edx
  mov dword [mem32], edi
  mov dword [mem32], esi
  mov dword [mem32], ebp
  mov dword [mem32], esp
  mov dword [mem32], r8d
  mov dword [mem32], r9d
  mov dword [mem32], r10d
  mov dword [mem32], r11d
  mov dword [mem32], r12d
  mov dword [mem32], r13d
  mov dword [mem32], r14d
  mov dword [mem32], r15d


; mov r32,m32

  mov eax, dword [mem32]
  mov ebx, dword [mem32]
  mov ecx, dword [mem32]
  mov edx, dword [mem32]
  mov edi, dword [mem32]
  mov esi, dword [mem32]
  mov ebp, dword [mem32]
  mov esp, dword [mem32]
  mov r8d, dword [mem32]
  mov r9d, dword [mem32]
  mov r10d, dword [mem32]
  mov r11d, dword [mem32]
  mov r12d, dword [mem32]
  mov r13d, dword [mem32]
  mov r14d, dword [mem32]
  mov r15d, dword [mem32]


; mov r32,i32

  mov eax, imm32
  mov ebx, imm32
  mov ecx, imm32
  mov edx, imm32
  mov edi, imm32
  mov esi, imm32
  mov ebp, imm32
  mov esp, imm32
  mov r8d, imm32
  mov r9d, imm32
  mov r10d, imm32
  mov r11d, imm32
  mov r12d, imm32
  mov r13d, imm32
  mov r14d, imm32
  mov r15d, imm32


; mov m32,i32

  mov dword [mem32], imm32


; mov r64,r64

  mov rax, rax
  mov rax, rbx
  mov rax, rcx
  mov rax, rdx
  mov rax, rdi
  mov rax, rsi
  mov rax, rbp
  mov rax, rsp
  mov rax, r8
  mov rax, r9
  mov rax, r10
  mov rax, r11
  mov rax, r12
  mov rax, r13
  mov rax, r14
  mov rax, r15
  mov rbx, rax
  mov rbx, rbx
  mov rbx, rcx
  mov rbx, rdx
  mov rbx, rdi
  mov rbx, rsi
  mov rbx, rbp
  mov rbx, rsp
  mov rbx, r8
  mov rbx, r9
  mov rbx, r10
  mov rbx, r11
  mov rbx, r12
  mov rbx, r13
  mov rbx, r14
  mov rbx, r15
  mov rcx, rax
  mov rcx, rbx
  mov rcx, rcx
  mov rcx, rdx
  mov rcx, rdi
  mov rcx, rsi
  mov rcx, rbp
  mov rcx, rsp
  mov rcx, r8
  mov rcx, r9
  mov rcx, r10
  mov rcx, r11
  mov rcx, r12
  mov rcx, r13
  mov rcx, r14
  mov rcx, r15
  mov rdx, rax
  mov rdx, rbx
  mov rdx, rcx
  mov rdx, rdx
  mov rdx, rdi
  mov rdx, rsi
  mov rdx, rbp
  mov rdx, rsp
  mov rdx, r8
  mov rdx, r9
  mov rdx, r10
  mov rdx, r11
  mov rdx, r12
  mov rdx, r13
  mov rdx, r14
  mov rdx, r15
  mov rdi, rax
  mov rdi, rbx
  mov rdi, rcx
  mov rdi, rdx
  mov rdi, rdi
  mov rdi, rsi
  mov rdi, rbp
  mov rdi, rsp
  mov rdi, r8
  mov rdi, r9
  mov rdi, r10
  mov rdi, r11
  mov rdi, r12
  mov rdi, r13
  mov rdi, r14
  mov rdi, r15
  mov rsi, rax
  mov rsi, rbx
  mov rsi, rcx
  mov rsi, rdx
  mov rsi, rdi
  mov rsi, rsi
  mov rsi, rbp
  mov rsi, rsp
  mov rsi, r8
  mov rsi, r9
  mov rsi, r10
  mov rsi, r11
  mov rsi, r12
  mov rsi, r13
  mov rsi, r14
  mov rsi, r15
  mov rbp, rax
  mov rbp, rbx
  mov rbp, rcx
  mov rbp, rdx
  mov rbp, rdi
  mov rbp, rsi
  mov rbp, rbp
  mov rbp, rsp
  mov rbp, r8
  mov rbp, r9
  mov rbp, r10
  mov rbp, r11
  mov rbp, r12
  mov rbp, r13
  mov rbp, r14
  mov rbp, r15
  mov rsp, rax
  mov rsp, rbx
  mov rsp, rcx
  mov rsp, rdx
  mov rsp, rdi
  mov rsp, rsi
  mov rsp, rbp
  mov rsp, rsp
  mov rsp, r8
  mov rsp, r9
  mov rsp, r10
  mov rsp, r11
  mov rsp, r12
  mov rsp, r13
  mov rsp, r14
  mov rsp, r15
  mov r8, rax
  mov r8, rbx
  mov r8, rcx
  mov r8, rdx
  mov r8, rdi
  mov r8, rsi
  mov r8, rbp
  mov r8, rsp
  mov r8, r8
  mov r8, r9
  mov r8, r10
  mov r8, r11
  mov r8, r12
  mov r8, r13
  mov r8, r14
  mov r8, r15
  mov r9, rax
  mov r9, rbx
  mov r9, rcx
  mov r9, rdx
  mov r9, rdi
  mov r9, rsi
  mov r9, rbp
  mov r9, rsp
  mov r9, r8
  mov r9, r9
  mov r9, r10
  mov r9, r11
  mov r9, r12
  mov r9, r13
  mov r9, r14
  mov r9, r15
  mov r10, rax
  mov r10, rbx
  mov r10, rcx
  mov r10, rdx
  mov r10, rdi
  mov r10, rsi
  mov r10, rbp
  mov r10, rsp
  mov r10, r8
  mov r10, r9
  mov r10, r10
  mov r10, r11
  mov r10, r12
  mov r10, r13
  mov r10, r14
  mov r10, r15
  mov r11, rax
  mov r11, rbx
  mov r11, rcx
  mov r11, rdx
  mov r11, rdi
  mov r11, rsi
  mov r11, rbp
  mov r11, rsp
  mov r11, r8
  mov r11, r9
  mov r11, r10
  mov r11, r11
  mov r11, r12
  mov r11, r13
  mov r11, r14
  mov r11, r15
  mov r12, rax
  mov r12, rbx
  mov r12, rcx
  mov r12, rdx
  mov r12, rdi
  mov r12, rsi
  mov r12, rbp
  mov r12, rsp
  mov r12, r8
  mov r12, r9
  mov r12, r10
  mov r12, r11
  mov r12, r12
  mov r12, r13
  mov r12, r14
  mov r12, r15
  mov r13, rax
  mov r13, rbx
  mov r13, rcx
  mov r13, rdx
  mov r13, rdi
  mov r13, rsi
  mov r13, rbp
  mov r13, rsp
  mov r13, r8
  mov r13, r9
  mov r13, r10
  mov r13, r11
  mov r13, r12
  mov r13, r13
  mov r13, r14
  mov r13, r15
  mov r14, rax
  mov r14, rbx
  mov r14, rcx
  mov r14, rdx
  mov r14, rdi
  mov r14, rsi
  mov r14, rbp
  mov r14, rsp
  mov r14, r8
  mov r14, r9
  mov r14, r10
  mov r14, r11
  mov r14, r12
  mov r14, r13
  mov r14, r14
  mov r14, r15
  mov r15, rax
  mov r15, rbx
  mov r15, rcx
  mov r15, rdx
  mov r15, rdi
  mov r15, rsi
  mov r15, rbp
  mov r15, rsp
  mov r15, r8
  mov r15, r9
  mov r15, r10
  mov r15, r11
  mov r15, r12
  mov r15, r13
  mov r15, r14
  mov r15, r15


; mov m64,r64

  mov qword [mem64], rax
  mov qword [mem64], rbx
  mov qword [mem64], rcx
  mov qword [mem64], rdx
  mov qword [mem64], rdi
  mov qword [mem64], rsi
  mov qword [mem64], rbp
  mov qword [mem64], rsp
  mov qword [mem64], r8
  mov qword [mem64], r9
  mov qword [mem64], r10
  mov qword [mem64], r11
  mov qword [mem64], r12
  mov qword [mem64], r13
  mov qword [mem64], r14
  mov qword [mem64], r15


; mov r64,m64

  mov rax, qword [mem64]
  mov rbx, qword [mem64]
  mov rcx, qword [mem64]
  mov rdx, qword [mem64]
  mov rdi, qword [mem64]
  mov rsi, qword [mem64]
  mov rbp, qword [mem64]
  mov rsp, qword [mem64]
  mov r8, qword [mem64]
  mov r9, qword [mem64]
  mov r10, qword [mem64]
  mov r11, qword [mem64]
  mov r12, qword [mem64]
  mov r13, qword [mem64]
  mov r14, qword [mem64]
  mov r15, qword [mem64]


; mov r64,i64

  mov rax, imm64
  mov rbx, imm64
  mov rcx, imm64
  mov rdx, imm64
  mov rdi, imm64
  mov rsi, imm64
  mov rbp, imm64
  mov rsp, imm64
  mov r8, imm64
  mov r9, imm64
  mov r10, imm64
  mov r11, imm64
  mov r12, imm64
  mov r13, imm64
  mov r14, imm64
  mov r15, imm64

  mov rax, 60
  mov rdi, 0
  syscall
