# The exit status  of an arithmetic expression is not an error value

(( 0 && 1 ))    # logical AND
echo $?         # 1

# And so ...
let "num = (( 0 && 1 ))"
echo $num       # 0

# But ...
let "num = (( 0 && 1 ))"
echo $?         # 1


(( 200 || 11 )) # logical OR
echo $?         # 0
# ...
let "num = (( 200 || 11 ))"
echo $num       # 1
let "num = (( 200 || 11 ))"
echo $?         # 0


(( 200 | 11))   # Bitwise OR
echo $?         # 0

let "num = (( 200 | 11 ))"
echo $num       # 203

# The "let" construct returns the same exit status
# as the double-parentheses arithmetic expansion


var=-2 && (( var+=2 ))
echo $?                 # 1
echo $var               # 0


var=-2 && (( var+=2 )) && echo $var # will not echo $var!
echo $?


