# use 'bc' for floating point arithmetic

a=1.5
let "b = $a + 1.3" 2>/dev/null  # error 1.3???
echo "b = $b" # b = 



