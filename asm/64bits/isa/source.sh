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
r16=(ax bx cx dx di si bp sp r8w r9w r10w r11w r12w r13w r14w r15w)
r32=(eax ebx ecx edx edi esi ebp esp r8d r9d r10d r11d r12d r13d r14d r15d)
r64=(rax rbx rcx rdx rdi rsi rbp rsp r8 r9 r10 r11 r12 r13 r14 r15)


echo "section  .data"                 >   $out
echo "  mem8  db 0x00"                >>  $out   
echo "  mem16 dw 0x0000"              >>  $out   
echo "  mem32 dd 0x00000000"          >>  $out   
echo "  mem64 dq 0x0000000000000000"  >>  $out   
echo                                  >>  $out
echo "  imm8  equ 0x11"               >>  $out
echo "  imm16 equ 0x1122"             >>  $out
echo "  imm32 equ 0x11223344"         >>  $out
echo "  imm64 equ 0x1122334455667788" >>  $out
echo                                  >>  $out
echo "section  .text"                 >>  $out
echo "global _start"                  >>  $out
echo                                  >>  $out
echo "_start:"                        >>  $out

# op r8,r8
echo                      >>  $out
echo "; $opcode r8,r8"    >>  $out
echo                      >>  $out
for i in ${r8[@]}
do
  for j in ${r8[@]}
  do
    echo "  ${opcode} $i, $j" >> $out
  done
done
echo                      >>  $out

# op m8,r8
echo                      >>  $out
echo "; $opcode m8,r8"    >>  $out
echo                      >>  $out
for i in ${r8[@]}
do
  echo "  ${opcode} byte [mem8], $i"    >> $out
done
echo                      >>  $out

# op r8,m8
echo                      >>  $out
echo "; $opcode r8,m8"    >>  $out
echo                      >>  $out
for i in ${r8[@]}
do
  echo "  ${opcode} $i, byte [mem8]"    >> $out
done
echo                      >>  $out

# op r8,i8
echo                      >>  $out
echo "; $opcode r8,i8"    >>  $out
echo                      >>  $out
for i in ${r8[@]}
do
  echo "  ${opcode} $i, imm8"    >> $out
done
echo                      >>  $out

# op m8,i8
echo                      >>  $out
echo "; $opcode m8,i8"    >>  $out
echo                      >>  $out
echo "  ${opcode} byte [mem8], imm8"    >> $out
echo                      >>  $out


# op r16,r16
echo                      >>  $out
echo "; $opcode r16,r16"  >>  $out
echo                      >>  $out
for i in ${r16[@]}
do
  for j in ${r16[@]}
  do
    echo "  ${opcode} $i, $j" >> $out
  done
done
echo                      >>  $out

# op m16,r16
echo                      >>  $out
echo "; $opcode m16,r16"  >>  $out
echo                      >>  $out
for i in ${r16[@]}
do
  echo "  ${opcode} word [mem16], $i"    >> $out
done
echo                      >>  $out

# op r16,m16
echo                      >>  $out
echo "; $opcode r16,m16"  >>  $out
echo                      >>  $out
for i in ${r16[@]}
do
  echo "  ${opcode} $i, word [mem16]"    >> $out
done
echo                      >>  $out

# op r16,i16
echo                      >>  $out
echo "; $opcode r16,i16"    >>  $out
echo                      >>  $out
for i in ${r16[@]}
do
  echo "  ${opcode} $i, imm16"    >> $out
done
echo                      >>  $out

# op m16,i16
echo                      >>  $out
echo "; $opcode m16,i16"  >>  $out
echo                      >>  $out
echo "  ${opcode} word [mem16], imm16"    >> $out
echo                      >>  $out


# op r32,r32
echo                      >>  $out
echo "; $opcode r32,r32"  >>  $out
echo                      >>  $out
for i in ${r32[@]}
do
  for j in ${r32[@]}
  do
    echo "  ${opcode} $i, $j" >> $out
  done
done
echo                      >>  $out

# op m32,r32
echo                      >>  $out
echo "; $opcode m32,r32"  >>  $out
echo                      >>  $out
for i in ${r32[@]}
do
  echo "  ${opcode} dword [mem32], $i"    >> $out
done
echo                      >>  $out

# op r32,m32
echo                      >>  $out
echo "; $opcode r32,m32"  >>  $out
echo                      >>  $out
for i in ${r32[@]}
do
  echo "  ${opcode} $i, dword [mem32]"    >> $out
done
echo                      >>  $out


# op r32,i32
echo                      >>  $out
echo "; $opcode r32,i32"  >>  $out
echo                      >>  $out
for i in ${r32[@]}
do
  echo "  ${opcode} $i, imm32"    >> $out
done
echo                      >>  $out

# op m32,i32
echo                      >>  $out
echo "; $opcode m32,i32"  >>  $out
echo                      >>  $out
echo "  ${opcode} dword [mem32], imm32"    >> $out
echo                      >>  $out


# op r64,r64
echo                      >>  $out
echo "; $opcode r64,r64"  >>  $out
echo                      >>  $out
for i in ${r64[@]}
do
  for j in ${r64[@]}
  do
    echo "  ${opcode} $i, $j" >> $out
  done
done
echo                      >>  $out

# op m64,r64
echo                      >>  $out
echo "; $opcode m64,r64"  >>  $out
echo                      >>  $out
for i in ${r64[@]}
do
  echo "  ${opcode} qword [mem64], $i"    >> $out
done
echo                      >>  $out

# op r64,m64
echo                      >>  $out
echo "; $opcode r64,m64"  >>  $out
echo                      >>  $out
for i in ${r64[@]}
do
  echo "  ${opcode} $i, qword [mem64]"    >> $out
done
echo                      >>  $out


if [ "$opcode" = "mov" ] 
then 
  # op r64,64
  echo                      >>  $out
  echo "; $opcode r64,i64"  >>  $out
  echo                      >>  $out
  for i in ${r64[@]}
  do
    echo "  ${opcode} $i, imm64"    >> $out
  done
  echo                      >>  $out
fi



echo "  mov rax, 60"      >>  $out
echo "  mov rdi, 0"       >>  $out
echo "  syscall"          >>  $out

run=0
if [ $run -eq "1" ]
then
  echo
  echo "$out:"
  echo
  echo "assembling..."
  yasm -f elf64 $out
  echo "linking..."
  ld $opcode.o
  echo "running..."
  ./a.out
  echo "cleaning up ..."
  rm -f a.out
  rm -f *.o
fi




