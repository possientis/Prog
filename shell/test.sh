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

file=/etc/passwd

if [[ -e $file ]]               # bash only, [[ more versatile than [
then
  echo "Password file exists."
else
  echo "Password file does not exist."
fi

if [ -e $file ]
then
  echo "Password file exists."
else
  echo "Password file does not exist."
fi


# [[ Octal and Hexadecimal evaluation ]]

decimal=15
octal=017
hex=0x0f

if [ "$decimal" -eq "$octal" ]
then
  echo "$decimal equals $octal"
else
  echo "$decimal is not equal to $octal"
fi  # 15 is not equal to 017 (does not evaluate within [ single brackets ] )

if [[ "$decimal" -eq "$octal" ]]
then
  echo "$decimal equals $octal"
else
  echo "$decimal is not equal to $octal"
fi  # 15 equals to 017 (evaluates within [[ double brackets ]] )

if [[ "$decimal" -eq "$hex" ]]
then
  echo "$decimal equals $hex"
else
  echo "$decimal is not equal to $hex"
fi  # 15 equals0x0f (evaluates within [[ double brackets ]] )


dir=/home/bozo

if cd "$dir" 2>/dev/null; then
  echo "Now in $dir"
else
  echo "Can't change to $dir"
fi

var1=20
var2=22
[ "$var1" -ne "$var2" ] && echo "$var1 is not equal to $var2"

[ -d "$dir" ] || echo "$dir directory does not exist."














