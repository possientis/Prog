#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits/hello
cd ${HOME}


option=$(sh option.sh)

# Hello world!
echo
echo -n "32 bits system call with AT&T syntax:     "
./as.sh hello_32bits.s; ld hello_32bits.o; ./a.out; ./clean.sh    

echo -n "64 bits system call with AT&T syntax:     "
./as.sh hello_syscall.s; ld hello_syscall.o; ./a.out; ./clean.sh  

echo -n "C library write call with AT&T syntax:    "
./as.sh hello_write.s; gcc $option hello_write.o; ./a.out; ./clean.sh  

echo -n "printf via macro with AT&T syntax:        "
./as.sh hello_macro.s; gcc $option hello_macro.o; ./a.out; ./clean.sh

echo -n "printf via function with AT&T syntax:     "
./as.sh print_string.s
./as.sh hello_function.s 
gcc $option hello_function.o print_string.o; ./a.out; ./clean.sh

echo -n "C program via AT&T assembly function:     "
./as.sh print_string.s
gcc $option hello_function.c print_string.o; ./a.out; ./clean.sh

echo -n "C++ program via AT&T assembly function:   "
./as.sh print_string.s
g++ $option hello_function.cpp print_string.o; ./a.out; ./clean.sh

echo 
echo -n "1 argument printf call with AT&T syntax:  "
./as.sh hello_printf_0.s; gcc $option hello_printf_0.o; ./a.out; ./clean.sh

echo -n "2 arguments printf call with AT&T syntax: "
./as.sh hello_printf_1.s; gcc $option hello_printf_1.o; ./a.out; ./clean.sh

echo -n "3 arguments printf call with AT&T syntax: "
./as.sh hello_printf_2.s; gcc $option hello_printf_2.o; ./a.out; ./clean.sh

echo -n "4 arguments printf call with AT&T syntax: "
./as.sh hello_printf_3.s; gcc $option hello_printf_3.o; ./a.out; ./clean.sh

echo -n "5 arguments printf call with AT&T syntax: "
./as.sh hello_printf_4.s; gcc $option hello_printf_4.o; ./a.out; ./clean.sh

echo -n "6 arguments printf call with AT&T syntax: "
./as.sh hello_printf_5.s; gcc $option hello_printf_5.o; ./a.out; ./clean.sh

echo -n "7 arguments printf call with AT&T syntax: "
./as.sh hello_printf_6.s; gcc $option hello_printf_6.o; ./a.out; ./clean.sh

echo -n "8 arguments printf call with AT&T syntax: "
./as.sh hello_printf_7.s; gcc $option hello_printf_7.o; ./a.out; ./clean.sh

echo

echo -n "32 bits system call with Intel syntax:    "
./yasm.sh hello_32bits.asm; ld hello_32bits.o; ./a.out; ./clean.sh    

echo -n "64 bits system call with Intel syntax:    "
./yasm.sh hello_syscall.asm; ld hello_syscall.o; ./a.out; ./clean.sh 

echo -n "C library write call with Intel syntax:   "
./yasm.sh hello_write.asm; gcc $option hello_write.o; ./a.out; ./clean.sh   

echo -n "printf via macro with Intel syntax:       "
./yasm.sh hello_macro.asm; gcc $option hello_macro.o; ./a.out; ./clean.sh

echo -n "printf via function with Intel syntax:    "
./yasm.sh print_string.asm
./yasm.sh hello_function.asm 
gcc $option hello_function.o print_string.o; ./a.out; ./clean.sh


echo -n "C program via Intel assembly function:    "
./yasm.sh print_string.asm
gcc $option hello_function.c print_string.o; ./a.out; ./clean.sh

echo -n "C++ program via Intel assembly function:  "
./yasm.sh print_string.asm
g++ $option hello_function.cpp print_string.o; ./a.out; ./clean.sh


echo 

echo -n "1 argument printf call with Intel syntax: "
./yasm.sh hello_printf_0.asm; gcc $option hello_printf_0.o; ./a.out; ./clean.sh

echo -n "2 arguments printf call with Intel syntax:"
./yasm.sh hello_printf_1.asm; gcc $option hello_printf_1.o; ./a.out; ./clean.sh 

echo -n "3 arguments printf call with Intel syntax:"
./yasm.sh hello_printf_2.asm; gcc $option hello_printf_2.o; ./a.out; ./clean.sh

echo -n "4 arguments printf call with Intel syntax:"
./yasm.sh hello_printf_3.asm; gcc $option hello_printf_3.o; ./a.out; ./clean.sh

echo -n "5 arguments printf call with Intel syntax:"
./yasm.sh hello_printf_4.asm; gcc $option hello_printf_4.o; ./a.out; ./clean.sh

echo -n "6 arguments printf call with Intel syntax:"
./yasm.sh hello_printf_5.asm; gcc $option hello_printf_5.o; ./a.out; ./clean.sh

echo -n "7 arguments printf call with Intel syntax:"
./yasm.sh hello_printf_6.asm; gcc $option hello_printf_6.o; ./a.out; ./clean.sh

echo -n "8 arguments printf call with Intel syntax:"
./yasm.sh hello_printf_7.asm; gcc $option hello_printf_7.o; ./a.out; ./clean.sh

cd ${DIR}
echo
echo "test completed successfully"
echo




