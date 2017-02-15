#!/bin/sh

while true
do
  unset K1 K2 K3
  read -s -N1
  K1="$REPLY"
  read -s -N2 -t 0.01
  K2="$REPLY"
  read -s -N1 -t 0.01
  K3="$REPLY"
  key="$K1$K2$K3"
  echo "key = $key"
done
