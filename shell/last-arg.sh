args=$#   # number of args passed

lastarg1=${!args}  # cannot use '$args' inside ${...}
lastarg2=${!#}


echo
echo "The last command-line argument is $lastarg1"
echo "The last command-line argument is $lastarg2"

exit 0
