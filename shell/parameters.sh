#/bin/bash

MINPARAMS=10

echo

echo "The name of this script is \"$0\"."

# Adds ./ for current directory
echo "The name of this script is \"`basename $0`\"."

echo

if [ -n "$1" ]              # tested variable is quoted
then
  echo "Parameter #1 is $1" # Need quotes to escape #
fi


if [ -n "$2" ]              # tested variable is quoted
then
  echo "Parameter #2 is $2" # Need quotes to escape #
fi


if [ -n "$3" ]              # tested variable is quoted
then
  echo "Parameter #3 is $3" # Need quotes to escape #
fi

echo "..."

if [ -n "${10}" ]           # Parameters > $9 must be enclosed in {brackets}
then
  echo "Parameter #10 is ${10}"
fi

echo "-----------------------------------"
echo "All the command-line parameters are: "$*""

if [ $# -lt "$MINPARAMS" ]
then
  echo
  echo "This script needs at least $MINPARAMS command-line arguments!"
fi

echo

exit 0


