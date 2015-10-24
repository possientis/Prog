#!/bin/sh
echo '\nThis is Haskell ...'
ghc -v0 pascal.hs 
./pascal
rm pascal.hi
rm pascal.o
rm pascal

echo '\nThis is Scheme ...'
./pascal.scm

echo '\nThis is Python ...'
./pascal.py

echo '\nThis is Java ...'
javac Pascal.java
java Pascal
rm Pascal.class

echo '\nThis is C# ...'
mcs pascal.cs
mono pascal.exe
rm pascal.exe

