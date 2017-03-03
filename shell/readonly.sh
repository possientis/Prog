readonly var1=1
declare -r var2=2
typeset -r var3=3


echo "var1 = $var1"
echo "var2 = $var2"
echo "var3 = $var3"

let "var1 += 1"   # readonly.sh: line 10: var1: readonly variable
(( var2++ ))      # readonly.sh: line 11: var2: readonly variable
let "var3 += 1"   # readonly.sh: line 12: var3: readonly variable





echo  # $? = 0
