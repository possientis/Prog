# sh or bash

echo --$1--
echo "--$1--"

if [ "$1" = hi ]; then
  echo 'The first argument was "hi"'
else
  echo -n 'The first argument was not "hi" -- '
  echo it was '"'$1'"'
fi
