#!/bin/sh

echo
echo -n "hostname: "
hostname
gcc $1 $2; ./a.out; rm a.out

echo
echo -n "hostname: "
ssh left hostname
ssh left mkdir /home/john/try
scp $1 left:/home/john/try/$1 > /dev/null
ssh left gcc /home/john/try/$1 $2 -o /home/john/try/a.out
ssh left /home/john/try/a.out
ssh left rm /home/john/try -r


echo
echo -n "hostname: "
ssh pi@berry hostname
ssh pi@berry mkdir /home/pi/try
scp $1 pi@berry:/home/pi/try/$1 > /dev/null
ssh pi@berry gcc /home/pi/try/$1 $2 -o /home/pi/try/a.out
ssh pi@berry /home/pi/try/a.out
ssh pi@berry rm /home/pi/try -r
