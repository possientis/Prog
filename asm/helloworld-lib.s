  .section .data
helloworld:
  .ascii "Hello, world!\n\0"
  .section .text
  .globl main #'main' rather than '_start' for linking from 'gcc' rather than 'ld'
main:           
  pushl $helloworld
  call printf

  pushl $0
  call exit
