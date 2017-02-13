if [ "$1" = "hi" ]; then
  echo 'The first argument was "hi"'
elif [ "$2" = "bye" ]; then
  echo 'The second argument was "bye"'
else
  echo -n 'The first argument was not "hi" and the second argument was not "bye"'
  echo -- They were '"'$1'"' and '"'$2'"'
fi
