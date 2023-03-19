        segment .text
        global array_create
        extern malloc


;       array = array_create ( size );

array_create:
        push  rbp
        mov   rbp, rsp 
        imul  rdi, 4    ; argument for malloc call
        call malloc     ; returned pointer in rax
        leave
        ret


