# counting to 11 in 10 different ways

n=1; echo -n "$n "

let "n = $n +1"
echo -n "$n "

# ':' (nop) important so we dont try to execute the command '3' 
: $((n = $n + 1))
echo -n "$n "

(( n = n + 1 ))
echo -n "$n "

n=$(($n + 1))
echo -n "$n "

: $[ n = $n + 1 ]
echo -n "$n "

n=$[ $n + 1 ]
echo -n "$n "


let "n++"
echo -n "$n "

(( n++ ))       # ++n also works
echo -n "$n "

: $(( n++ ))
echo -n "$n "   # ++n ok

: $[ n++ ]
echo -n "$n "   # ++n ok

echo

exit 0

