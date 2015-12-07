#!/bin/sh

as -o hello.o hello.s
ld -s -o hello hello.o
./hello
#rm hello.o
rm hello

