#!/bin/sh

# using the C library requires linking with gcc after compiling with yasm or as.
# However on debian stretch gcc will fail on the object file produced by the
# assemblers, unless the '-no-pie' option is used (no position independent code).
# In order for this script to work both on debian stretch and debian jessie,
# we need to introduce a variable 'option' and set it to "-no-pie" for stretch

version=$(uname -a | cut -d' ' -f 8 | cut -d '.' -f 1)

if [ "$version" = "6" ]
then
  option="-no-pie -z noexecstack"
else
  echo "unsupported version"
  exit 1
fi

echo $option


