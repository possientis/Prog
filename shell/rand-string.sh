#!/bin/bash
# rand-string.sh

# Generating an 8-character "random" string.

if [ -n "$1" ]  #  If command-line argument present,
then            #+ then set start-string to it.
  str0="$1"
else
  str0="$$"     #  Else use PID of script as start-string.
fi

POS=2           # Starting from position 2 in the string.
LEN=8           # Extract eight characters.


str1=$( echo "$str0" | md5sum | md5sum )
#  Doubly scramble     ^^^^^^   ^^^^^^
#+ by piping and repiping to md5sum.

randstring="${str1:$POS:$LEN}"
# Can parameterize ^^^^ ^^^^

echo "$randstring"

exit $?
#  No, this is is not recommended
#+ as a method of generating hack-proof passwords
#  Because anyone reading this script and simply 
#  try out all the possible values of $$ and guess 
#  your password that way. In any case, 8 character
#  long password is hopelessly insecure
