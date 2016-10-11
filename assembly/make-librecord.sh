#!/bin/sh
as --32 read-record.s -o read-record.o
as --32 write-record.s -o write-record.o
ld -melf_i386 -shared read-record.o write-record.o -o librecord.so
rm read-record.o write-record.o
