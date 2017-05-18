if [ -n "$1" ] 
then
  opcode=$1
else
  echo "usage: source.sh <opcode>"
  exit 1
fi

prefix=source
out=$opcode.asm

r8=(al bl cl dl dil sil bpl spl r8b r9b r10b r11b r12b r13b r14b r15b)  


echo "section  .text"     >   $out
echo "global _start"      >>  $out
echo                      >>  $out
echo "_start:"            >>  $out
echo                      >>  $out

echo "; $opcode r8,r8"    >> $out
echo                      >>  $out
for i in ${r8[@]}
do
  for j in ${r8[@]}
  do
    echo "  ${opcode} $i, $j" >> $out
  done
done

echo "  mov rax, 60"      >>  $out
echo "  mov rdi, 0"       >>  $out
echo "  syscall"          >>  $out


cat $out
