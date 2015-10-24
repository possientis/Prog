#!/bin/sh

# running C++ version
echo '\n'
echo This is C++ ...
g++ -std=c++14 A.h B.h Main.c
./a.out
rm *.h.gch
rm a.out

# running java version
echo '\n'
echo This is Java ...
javac Main.java A.java B.java
java Main
rm *.class

# running C# version
echo '\n'
echo This is C# ...
mcs Main.cs A.cs B.cs
mono Main.exe
rm *.exe

# running Python version
echo '\n'
echo This is Python ...
./Main.py

# running Scheme version
echo '\n'
echo This is Scheme ...
./Main.scm

