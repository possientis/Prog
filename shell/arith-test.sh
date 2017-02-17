# (( ... )) construct evaluates and tests numerical expressions
# Exit status opposite from [ ... ] construct

(( 0 ))
echo "Exit status of \"(( 0 ))\" is $?."        # 1

(( 1 ))
echo "Exit status of \"(( 1 ))\" is $?."        # 0

(( 5 > 4 ))
echo "Exit status of \"(( 5 > 4 ))\" is $?."    # 0

(( 5 > 9 ))
echo "Exit status of \"(( 5 > 9 ))\" is $?."    # 1


(( 5 == 5 ))
echo "Exit status of \"(( 5 == 5 ))\" is $?."   # 0


(( 5 - 5 ))
echo "Exit status of \"(( 5 - 5 ))\" is $?."    # 1

(( 5 / 4 ))
echo "Exit status of \"(( 5 / 4 ))\" is $?."    # 0


(( 1 / 2 ))
echo "Exit status of \"(( 1 / 2 ))\" is $?."    # 1


(( 1 / 0 )) 2>/dev/null
echo "Exit status of \"(( 1 / 0 ))\" is $?."    # 1

# (( ... )) also useful in an if-then test

var1=5
var2=4

if (( var1 > var2 ))  # not $var1, $var2, why?
then
  echo "$var1 is greater than $var2"
fi

exit 0
