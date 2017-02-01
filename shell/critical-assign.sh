# This will prevent an error when positional parameter is absent
variable1_=$1_  # rather than variable1=$1
variable2=$2

echo
echo "variable1_ = $variable1_"
echo "variable2 = $variable2"

critical_argument01=$variable1_

# The extra character can be stripped off later, like so:
variable1=${variable1_/_/}

echo "variable1 = $variable1"

#   A more straightforward way of dealing with this is
#+  to simply test whether expected positional parameters have been passed 

if [ -z "$1" ]
then
  echo "Parameter #1 is missing"
fi

if [ -n "$1" ]
then
  echo "Parameter #1 is present"
fi



