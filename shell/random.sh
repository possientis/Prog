#!/bin/bash

# $RANDOM returns a different random integer at each invocation.
# Nominal range: 0 - 32767 (signed 16-bit integer).

MAXCOUNT=10
count=1

echo
echo "$MAXCOUNT random numbers:"
echo "-----------------"
while [ "$count" -le $MAXCOUNT ]
  # Generate 10 ($MAXCOUNT) random integers.
do
  number=$RANDOM  # 0 - 32767
  echo $number
  let "count += 1" # Increment count.
done
echo "-----------------"

# If you need a random int within a certain range, use the 'modulo' operator.


AWKSCRIPT=' { srand(); print rand() } '

echo -n "Random number between 0 and 1 = "

echo | awk "$AWKSCRIPT"   
# what happens if you leave out the 'echo' ?
# Piping an empty "echo" to awk gives it dummy input,
#+ and thus makes it unnecessary to supply a filename.

exit 0



