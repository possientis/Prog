#!/bin/sh

# returns generated code for single at&t assembly instruction

# e.g.
# $ ./att.sh xor %rax, %rax
# 48 31 c0 xor %rax,%rax

# note that you need to escape '$' on input:
# e.g.
# $ ./att.sh movq \$2, %rax
# 48 c7 c0 02 00 00 00 mov $0x2,%rax

argument=$(echo "$@" | sed 's/att.sh/%/g' -)

echo ".section .text" >  log.s
echo ".global _start" >> log.s
echo "_start:"        >> log.s 
echo "$argument"      >> log.s
echo "movq \$60,%rax" >> log.s
echo "movq \$0, %rdi" >> log.s
echo "syscall"        >> log.s

as -o log.o log.s
ld -o log log.o
objdump -d log > log1

for w in "$(cat log1 | grep -A1 _start | grep -v _start | cut -d':' -f2)"
do
  echo -n $w
done
echo

rm -f log.s log.o log log1
