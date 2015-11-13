#!/bin/sh

echo '\nThis is Java ...'
javac Builder.java; java Builder; rm *.class

echo '\nThis is C# ...'
mcs builder.cs; mono builder.exe; rm builder.exe
