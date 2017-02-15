echo

if test -z "$1"
then
  echo "No command-line arguments."
else
  echo "First command-line argument is $1."
fi

if /usr/bin/test -z "$1"  # equivalent to "test" builtin
#  ^^^^^^^^^^^^^          # specifying full pathname
then
  echo "No command-line arguments."
else
  echo "First command-line argument is $1."
fi

if [ -z "$1" ]  # same thing
then
  echo "No command-line arguments."
else
  echo "First command-line argument is $1."
fi


if /usr/bin/[ -z "$1" ]  # same as builtin
then
  echo "No command-line arguments."
else
  echo "First command-line argument is $1."
fi
