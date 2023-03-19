          segment .data
name      db      "Calvin", 0
address   db      "12 Mockingbird Lane", 0 
balance   dd      12500

          struc   Customer
c_id      resd    1     ; global field name      
c_name    resb    64    ; can use local field name '.name' then 'Customer.name'
c_address resb    64
;          align 4      ; may need to use 'align' to fit C struct alignment
c_balance resd    1 
          endstruc 

c         dq      0

          segment .text
          global  main
          extern  malloc, strcpy

main:
          push    rbp
          mov     rbp, rsp 
          sub     rsp, 32

          mov     rdi, Customer_size    ; yasm creates identifier from struct
          call    malloc
          mov     [c], rax              ; saving pointer to memory

          mov     [rax+c_id], dword 7
          lea     rdi, [rax+c_name]     ; destination     
          lea     rsi, [name]           ; source 
          call    strcpy

          mov     rax, [c]              ; restore pointer
          lea     rdi, [rax+c_address]  ; destination
          lea     rsi, [address]        ; source
          call    strcpy
  
          mov     rax, [c]              ; restore pointer
          mov     edx, [balance]
          mov     [rax+c_balance], edx
end:
          xor     eax, eax
          leave
          ret
    
