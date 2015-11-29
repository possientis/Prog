#!/bin/sh

echo '\nThis is Java ...'
javac Prototype.java; java Prototype; rm Prototype.class

echo '\nThis is C# ...'
mcs prototype.cs; mono prototype.exe; rm prototype.exe

