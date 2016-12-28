; Program : exit

; Executes the exit system call

; No input

; Output : only the exit status ($? in the shell)
;

segment .text
global _start ; can use 'main' instead, but then link with gcc rather than ld

_start  :
  mov eax,1 ; 1 is the exit sys call number
  mov ebx,5 ; the status value to return
  int 0x80  ; execute a system call



