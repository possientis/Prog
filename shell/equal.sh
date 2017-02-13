if [ 01 = 1 ]; then         # not equal, string equality
  echo These are equal
else
  echo These are not equal
fi

if [ 01 -eq 1 ]; then
  echo These are equal
else
  echo These are not equal
fi

