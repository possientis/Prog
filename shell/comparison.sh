
# integer comparison

a=5
b=7

[ "$a" -eq "$a" ] && echo "$a is equal to $a"
[ ! "$a" -eq "$a" ] || echo "$a is equal to $a"
[ "$a" -ne "$a" ] || echo "$a is equal to $a"

echo

[ "$a" -eq "$b" ] || echo "$a is not equal to $b"
[ ! "$a" -eq "$b" ] && echo "$a is not equal to $b"
[ "$a" -ne "$b" ] && echo "$a is not equal to $b"

echo

[ "$b" -gt "$a" ] && echo "$b is greater than $a"
[ ! "$a" -ge "$b" ] && echo "$b is greater than $a" 
[ "$a" -ge "$b" ] || echo "$b is greater than $a" 
(("$b" > "$a")) && echo "$b is greater than $a" 
(("$a" >= "$b")) || echo "$b is greater than $a" 


echo

[ "$a" -lt "$b" ] && echo "$a is smaller than $b"
[ ! "$b" -le "$a" ] && echo "$a is smaller than $b" 
[ "$b" -le "$a" ] || echo "$a is smaller than $b" 
(("$a" < "$b")) && echo "$a is smaller than $b"
(("$b" <= "$a")) || echo "$a is smaller than $b"

# string comparison

echo; echo

a=abc
b=def

[ "$a" = "$a" ] && echo "\"$a\" is equal to \"$a\""
[ ! "$a" = "$a" ] || echo "\"$a\" is equal to \"$a\""
[ "$a" == "$a" ] && echo "\"$a\" is equal to \"$a\""
[ ! "$a" == "$a" ] || echo "\"$a\" is equal to \"$a\""
[ "$a" != "$a" ] || echo "\"$a\" is equal to \"$a\""
[ ! "$a" != "$a" ] & echo "\"$a\" is equal to \"$a\""

echo

[ "$a" = "$b" ] || echo "\"$a\" is different from \"$b\""
[ ! "$a" = "$b" ] &&  echo "\"$a\" is different from \"$b\""
[ "$a" == "$b" ] || echo "\"$a\" is different from \"$b\""
[ ! "$a" == "$b" ] &&  echo "\"$a\" is different from \"$b\""
[ "$a" != "$b" ] && echo "\"$a\" is different from \"$b\""
[ ! "$a" != "$b" ] || echo "\"$a\" is different from \"$b\""

echo

[[ "$a" == a* ]] && echo "\"$a\" starts with an 'a'"  # pattern matching
[[ "$a" == "a*" ]] || echo "\"$a\" is not the the string \"a*\"" 

[[ "$b" == d* ]] && echo "\"$b\" starts with an 'd'"  # pattern matching
[[ "$b" == "d*" ]] || echo "\"$b\" is not the the string \"d*\"" 

[[ "$a" < "$b" ]] && echo "\"$a\" is alphabetically prior to \"$b\""
# < needs to be escaped within [...]
[ "$a" \< "$b" ] && echo "\"$a\" is alphabetically prior to \"$b\""





