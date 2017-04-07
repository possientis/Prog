#!/bin/sh

version=$(uname -a | cut -d' ' -f 7 | cut -d '.' -f 1)

if [ "$version" = "4" ]   # debian stretch 
then
  gcj="gcj-6"
elif [ "$version" = "3" ] # debian jessie
then
  gcj="gcj-4.9"
else
  echo "unsupported version"
  exit 1
fi

echo $gcj


