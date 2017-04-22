
yasm -f elf64 shellcode.asm

out1=$(objdump -d -M intel shellcode.o | cut -d ':' -f 2)

for i in $out1; do echo $i; done



rm -f shellcode.o
