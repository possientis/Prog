      segment .text
      global copy_array

copy_array:

      xor ecx, ecx  ; rcx = 0

more:
      mov eax, [rsi+4*rcx]  ; rsi is second argument
      mov [rdi+4*rcx], eax  ; rdi is first argument
      add rcx, 1
      cmp rcx, rdx          ; rdx is third argument
      jne more
      xor eax, eax
      ret
