#!/bin/bash

g++ --version | head -n1

echo 'int main(){}' > dummy.c && g++ -o dummy dummy.c
if [ -x dummy ]
    then echo "g++ compilation OK";
    else echo "g++ compilation failed.";
fi
rm -f dummy.c dummy
