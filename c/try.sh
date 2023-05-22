#!/bin/sh

echo
echo -n "hostname: "
hostname
gcc $1 $2; ./a.out; rm a.out

echo
echo -n "hostname: "
ssh left hostname
ssh left mkdir ${HOME}/try
scp $1 left:${HOME}/try/$1 > /dev/null
ssh left gcc ${HOME}/try/$1 $2 -o ${HOME}/try/a.out
ssh left ${HOME}/try/a.out
ssh left rm ${HOME}/try -r


echo
echo -n "hostname: "
ssh pi@berry hostname
ssh pi@berry mkdir /home/pi/try
scp $1 pi@berry:/home/pi/try/$1 > /dev/null
ssh pi@berry gcc /home/pi/try/$1 $2 -o /home/pi/try/a.out
ssh pi@berry /home/pi/try/a.out
ssh pi@berry rm /home/pi/try -r
