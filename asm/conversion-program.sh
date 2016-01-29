as --32 integer-to-string.s -o integer-to-string.o
as --32 count-chars.s -o count-chars.o
as --32 write-newline.s -o write-newline.o
as --32 conversion-program.s -o conversion-program.o

ld -melf_i386 integer-to-string.o count-chars.o write-newline.o \
  conversion-program.o -o conversion-program

./conversion-program

rm conversion-program conversion-program.o
rm write-newline.o count-chars.o integer-to-string.o
