##########################################################################
# run as '$ . shellcode.sh' so variable SHELLCODE gets into environment. #
##########################################################################

# This script assembles the file shellcode.asm, then extracts the code 
# bytes and write then into the file shellcode.bin. It also creates a 
# file shellcode.c which declares the code bytes as an unsigned char []

yasm -f elf64 shellcode.asm

out1=$(objdump -d -M intel shellcode.o | cut -d ':' -f 2)
out2=$(for i in $out1; do echo $i; done | grep -Ev '[g-zA-Z]|(bad)')
out3=$(for i in $out2; do echo -n "\x${i}"; done)

echo -en "$out3" > shellcode.bin
echo "unsigned char shellcode[] = \"$out3\";"  >  shellcode.c

# if you have run '$ . shellcode.sh', variable SHELLCODE will be set
# i.e. it will be visible with the 'set' command.
SHELLCODE=$(perl -e 'print "\x90"x208')"$(cat shellcode.bin)"

# however, it still needs to be exported to be part of environment
# i.e. to become visible with the 'env' command.
export SHELLCODE

echo -n "$SHELLCODE" | xxd

rm -f shellcode.o
