#!/bin/sh

# A system information gathering script

# Command 1
UNAME="uname -a"
printf "Gathering system information with the $UNAME command: \n"
$UNAME


# Command 2
DISKSPACE="df -h"
printf "Gathering diskspace information with the $DISKSPACE command:\n"
$DISKSPACE
