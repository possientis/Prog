# This works with sh and bash

variable=$1

case "$variable" in
  abc)  echo "\$variable = abc" ;;  # double semicolon
  def)  echo "\$variable = def" ;;  # double semicolon 
esac


# case can perform pattern matching as follows:
case "$1" in
  bye)
    echo Fine, bye.
    ;;
  hi|hello)
    echo Nice to see you.
    ;;
  what*)
    echo Whatever.
    ;;
  *)
    echo 'Huh?'
    ;;
esac

