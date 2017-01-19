        segment .text
        global _start

_start:
        push rsp
        push rsp
        push rsp

        pop rsp
        pop rsp
        pop rsp
end:
        xor eax, eax
        ret
