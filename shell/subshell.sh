# sh or bash

a=123
( a=321; echo "a = $a" )  # subshell

echo "a = $a" # a = 123

# "a" within parenthesis acts like a local variable.


( cd uglydir; uglyprogram ; exit 0)

echo

# subshell with a small modification to env variables
(a="hello"; echo "a = $a"; exit 0)







