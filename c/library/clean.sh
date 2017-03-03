#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/library
cd ${HOME}

rm -f a.out
rm -f *.o
rm -f *.a
rm -f *.so
rm -f *.so.*
rm -f log
rm -f demo_use_static
rm -f demo_use
rm -f demo_dynamic

cd ${DIR}
