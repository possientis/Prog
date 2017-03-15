#!/bin/sh

echo
echo -n "hostname: "
hostname
gcc $1; ./a.out; rm a.out

echo
echo -n "hostname: "
ssh back hostname
ssh back mkdir /home/john/try
scp $1 back:/home/john/try/$1 > /dev/null
ssh back gcc /home/john/try/$1 -o /home/john/try/a.out
ssh back /home/john/try/a.out
ssh back rm /home/john/try -r


echo
echo -n "hostname: "
ssh pi@berry hostname
ssh pi@berry mkdir /home/pi/try
scp $1 pi@berry:/home/pi/try/$1 > /dev/null
ssh pi@berry gcc /home/pi/try/$1 -o /home/pi/try/a.out
ssh pi@berry /home/pi/try/a.out
ssh pi@berry rm /home/pi/try -r
