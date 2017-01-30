#!/bin/sh

objdump -d -M intel ./a.out | grep -A30 _start\>:
