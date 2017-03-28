var1=hello1
var2=hello2
var3=hello3

whichvar=var1

echo "whichvar is $whichvar"        # whichvar is var1
echo "${whichvar} is ${!whichvar}"  # var1 is hello1
