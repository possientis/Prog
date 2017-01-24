#!/bin/sh

objdump -d -M intel ./a.out | grep -A20 _start\>:
