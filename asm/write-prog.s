  .include "record-def.s"
  .include "linux.s"

  .section .data

# Constant data of the records we want to write 
# Each text data item is padded to the proper
# length with null (i.e. 0) bytes.

# .rept is used to pad each item. .rept tells
# the assembler to repeat the section between
# .rept and .endr the number of times specified.
# This is used in this program to add extra null
# characters at the end of each field to fill it up

record1:
  .ascii "Fredrick\0"  
  .rept 31                        # padding to 40 bytes
  .byte 0
  .endr

  .ascii "Bartlett\0"             # padding to 40 bytes
  .rept 31
  .byte 0
  .endr

  .ascii "4242 S Prairie\nTulsa, OK 55555\0"
  .rept 209                       # padding to 240 bytes
  .byte 0
  .endr

  .long 45

record2:
  .ascii "Marilyn\0"
  .rept 32                        # padding to 40 bytes
  .byte 0
  .endr

  .ascii "Taylor\0"
  .rept 33
  .byte 0
  .endr

  .ascii "2224 S Johannan St\nChicago, IL 12345\0"
  .rept 203
  .byte 0
  .endr

  .long 29

record3:
  .ascii "Derrick\0"
  .rept 32
  .byte 0
  .endr

  .ascii "McIntire\0"
  .rept 31
  .byte 0
  .endr

  .ascii "500 W Oakland\nSan Diego, CA 54321\0"
  .rept 206
  .byte 0
  .endr

  .long 36













