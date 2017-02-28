#!/bin/sh

# returns generated code for single intel assembly instruction

# e.g.
# $ ./intel.sh xor rax, rax
# 48 31 c0 xor rax,rax

# e.g.
# $ ./intel.sh mov rax, 2
# 48 c7 c0 02 00 00 00 mov rax,0x20 

echo "segment .text"  >  log.asm
echo "global _start"  >> log.asm
echo "_start:"        >> log.asm 
echo "$@"             >> log.asm
echo "mov rax, 60"    >> log.asm
echo "mov rdi, 0"     >> log.asm
echo "syscall"        >> log.asm

yasm -f elf64 log.asm
ld -o log log.o
objdump -d -M intel log > log1

for w in "$(cat log1 | grep -A1 _start | grep -v _start | cut -d':' -f2)"
do
  echo -n $w
done
echo

rm -f log.asm log.o log log1
