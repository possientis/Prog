        segment .data
switch: dq  _start.case0    ; outside _start, local label fully qualified
        dq  _start.case1    ; outside _start, local label fully qualified
        dq  _start.case2    ; outside _start, local label fully qualified
i:      dq  2

        segment .text
        global _start       ; tell linker about _start

_start:

        mov rax, [i]        ; move i to rax
        jmp [switch+rax*8]  ; switch(i)

.case0:                     ; defining local label .case0 (local to _start)
        mov rbx, 100        ; go here if i == 0 
        jmp .end            ; within _start, no need to fully qualify local label
.case1:                     ; defining local label .case1 (local to _start) 
        mov rbx, 101        ; go here if i == 1
        jmp .end            ; within _start, no need to fully qualify local label
.case2:                     ; defining local label .case2 (local to _start)
        mov rbx, 102        ; go here if i == 2

.end:                       ; defining local label .case3 (local to _start) 
        mov   eax, 1    ; sys call number
        mov   ebx, 0    ; returned status code
        int   0x80

