declare -r var1=1   # readonly var1=1
declare -i var2=2   # subsequent occurences of "var2" as an integer
var3=3

echo "var1 = $var1"

(( var1++ ))        # declare.sh: line 7: var1: readonly variable 

var2=abc
var3=abc
echo "var2 = $var2"   # var2 = 0   , was declared as an integer
echo "var3 = $var3"   # var3 = abc

var4=6/3
echo "var4 = $var4"   # var4 = 6/3 , string
declare -i var4
var4=6/3              # needs to be called again
echo "var4 = $var4"   # var4 = 2

declare -a var5       # treated as an array
var5[0]=abc
var5[1]=def
echo "var5[0] = ${var5[0]}" # var5[0] = abc
echo "var5[1] = ${var5[1]}" # var5[0] = abc

var6[0]=abc     # works too ????
var6[1]=def
echo "var6[0] = ${var6[0]}" # var6[0] = abc
echo "var6[1] = ${var6[1]}" # var6[0] = abc

function func()
{
  echo "func is running with argument $1"
}

func abc    # func is running with argument abc

declare -f  # generates listing of all functions defined in script

declare -x var1 # export


