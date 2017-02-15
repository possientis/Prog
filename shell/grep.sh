if grep -q 'daemon:x' /etc/passwd; then
  echo The daemon user is in the passwd file.
else
  echo There is a big problem. daemon is not in the passwd file.
fi



word=Linux
seq=inu

if echo "$word" | grep -q "$seq"
then
  echo "$seq found in $word"
else
  echo "$seq not found in $word"
fi

seq=inuX
if echo "$word" | grep -q "$seq"
then
  echo "$seq found in $word"
else
  echo "$seq not found in $word"
fi

