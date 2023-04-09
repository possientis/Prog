#!/bin/bash

sync

umount /dev/sda1
sleep 1

hdparm -y /dev/sda
sleep 3
