echo 
var[2]=abc  # creates an indexed array
echo "var[2]=${var[2]}"
echo "var[@]=${var[@]}"     # abc
echo "!var[@]=${!var[@]}"   # 2
unset var                   # destroy indexed array
echo "var[@]=${var[@]}"      


# indexed arrays can be declared
echo
declare -a var2
var2=(abc defg hijkl)
echo "var2[0]=${var2[0]}"
echo "var2[1]=${var2[1]}"
echo "var2[2]=${var2[2]}"
echo "var2[-1]=${var2[-1]}" # hijkl
echo "var2[-2]=${var2[-2]}" # defg
echo "var2[-3]=${var2[-3]}" # abc
echo "var2[@]=${var2[@]}"   # abc defg hijkl
echo "var2[*]=${var2[*]}"   # abc defg hijkl (single word if double quoted)
echo "!var2[@]=${!var2[@]}" # 0 1 2 , subscripts 
echo "#var2[0]=${#var2[0]}" # 3 , length of abc
echo "#var2[1]=${#var2[1]}" # 4 , length of defg
echo "#var2[2]=${#var2[2]}" # 5 , length of hijkl
echo "#var2[@]=${#var2[@]}" # 3 , length of array
unset var2                  # destroy indexed array
echo "var2[@]=${var2[@]}"  

echo
# associative arrays need to be declared as follows
declare -A name
# can be initialized as follows
name=([abc]=ABC [def]=DEF [ghi]=GHI)
echo "name[abc]=${name[abc]}"
echo "name[def]=${name[def]}"
echo "name[ghi]=${name[ghi]}" 
echo "name[@]=${name[@]}"   # DEF GHI ABC (order not meaningful)
echo "name[*]=${name[*]}"   # DEF GHI ABC (single world if double quoted)
echo "!name[@]=${!name[@]}" # def ghi abc (order matches values)
unset name                  # destroy associative array
echo "name[@]=${name[@]}"   # 

echo
declare -A name2
name2[abc]=ABC
name2[def]=DEF
name2[ghi]=GHI
echo "name2[abc]=${name2[abc]}"
echo "name2[def]=${name2[def]}"
echo "name2[ghi]=${name2[ghi]}" 
echo "name2[@]=${name2[@]}"   # DEF GHI ABC (order not meaningful)
echo "name2[*]=${name2[*]}"   # DEF GHI ABC (order not meaningful)
echo "!name2[@]=${!name2[@]}" # def ghi abc
unset name2                   # destroy associative array
echo "name2[@]=${name2[@]}"




