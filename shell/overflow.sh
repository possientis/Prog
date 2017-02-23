echo $BASH_VERSION

let "a=2**31 - 2" 
echo "a = $a" # a=2147483646
let "a+=1"
echo "a = $a" # a=2147483647
let "a+=1"
echo "a = $a" # a=2147483648

let "a=2**63 - 2" 
echo "a = $a" # a=9223372036854775806
let "a+=1"
echo "a = $a" # a=9223372036854775807
let "a+=1"    # overflow
echo "a = $a" # a=-9223372036854775808


