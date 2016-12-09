#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c#/
cd ${HOME}

mcs Sort.cs
mono Sort.exe
rm Sort.exe

cd ${DIR}
echo '\nAll c# tests completed successfully\n'




