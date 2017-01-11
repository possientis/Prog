        segment .data
a       dq  0x0102040810204080  ; xor of 8 bytes is 0xff


        segment .text
        global _start

_start:                         ; computes xor of 8 bytes
      
        mov rbx, [a]
        mov rax, 0              ; result
        mov rcx, 0xff           ; mask
        
        mov rdx, rbx
        and rdx, rcx
        mov rax, rdx            ; first byte

        ror rbx, 8              ; align second bytes 
        mov rdx, rbx
        and rdx, rcx
        xor rax, rdx            ; second byte

        ror rbx, 8              ; align third byte
        mov rdx, rbx
        and rdx, rcx
        xor rax, rdx            ; third byte

        ror rbx, 8
        mov rdx, rbx
        and rdx, rcx
        xor rax, rdx            ; fourth


        ror rbx, 8
        mov rdx, rbx
        and rdx, rcx
        xor rax, rdx            ; fifth


        ror rbx, 8
        mov rdx, rbx
        and rdx, rcx
        xor rax, rdx            ; sixth


        ror rbx, 8
        mov rdx, rbx
        and rdx, rcx
        xor rax, rdx            ; seventh


        ror rbx, 8
        mov rdx, rbx
        and rdx, rcx
        xor rax, rdx            ; eighth

        ror rbx, 8              ; restore to initial value

_exit:
        ret
