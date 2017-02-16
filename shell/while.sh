FILE=/tmp/while.$$

echo firstline > $FILE

while tail -10 $FILE | grep -q firstline; do
  echo -n Number of lines in $FILE:' '
  wc -l $FILE | awk '{print $1}'
  echo newline >> $FILE
done

rm -f $FILE
