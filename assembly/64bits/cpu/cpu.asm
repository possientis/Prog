section .bss
address dq    0

buffer  resb  state_size

        struc state
.rax    resq  1
        endstruc


section .text
global get_cpu_state
global set_cpu_state

get_cpu_state:
  mov [buffer+state.rax],  rax
  lea rax, [buffer]          
  ret

set_cpu_state:
  mov [address], rdi
  mov rax, [address + state.rax]
  mov [buffer + state.rax], rax
  ret 

  

