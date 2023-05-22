#!/bin/sh
# need to install mono-mcs

set -e 
DIR=${HOME}/Prog/c#/
cd ${DIR}

mcs Sort.cs
mono Sort.exe
rm Sort.exe

echo '\nAll c# tests completed successfully\n'




