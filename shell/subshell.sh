# sh or bash

a=123
( a=321; echo "a = $a" )  # subshell

echo "a = $a" # a = 123

# "a" within parenthesis acts like a local variable.


