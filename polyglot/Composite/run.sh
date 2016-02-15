#!/bin/sh
echo '\nThis is C ...'
gcc composite.c; ./a.out; rm a.out

echo '\nThis is Java ...'
javac Composite.java; java Composite; rm *.class
