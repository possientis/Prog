#!/bin/sh

echo '\nThis is C ...'
gcc filter.c; ./a.out 2>/dev/null; rm a.out;  # diverting stderr (debug info)

echo '\nThis is Java ...'
javac Filter.java; java Filter; rm *.class;
