# bash only

a=2334          # integer
let "a += 1"    
echo "a = $a"   # a = 2335
echo            # integer, still

b=${a/23/BB}    # substitute "BB" for "23"
                # This transforms $b into a string
echo "b = $b"   # b = BB35
declare -i b    # declaring it an integer does not help
echo "b = $b"   # b = BB35

let "b += 1"    # BB35 + 1
echo "b = $b"   # b = 1
echo            # bash sets the "integer value" of a string to 0

c=BB34
echo "c = $c"   # BB34
d=${c/BB/23}    # substitute "23" for "BB"
                # This transforms $d into an integer
echo "d = $d"   # d = 2334
let "d += 1"    # 2334 + 1
echo "d = $d"   # d = 2335
echo

# what about null variables?
e=''            # ... or e="" ... or e=
echo "e = $e"   # e = 
let "e += 1"    # Arithmetic operation allowed on null variable?
echo "e = $e"   # e = 1
echo            # Null variable transformed into an integer

# what about undeclared variable?
echo "f = $f"   # f =
let "f += 1"    # Arithmetic operation allowed?
echo "f = $f"   # f = 1
echo            # Undeclared variable transformed into an integer

# However ...
let "f /= $undecl_var"  # divide by zero?
# int-or-string.sh: line 41: let: f /= : syntax error: operand expected (error token is "/= ")
# Syntax error! Variable $undecl_var is not set to zero here!


# But still ...
let "f /= 0"
# int-or-string.sh: line 47: let: f /= 0: division by 0 (error token is "0")
# Expected behaviour

exit $?


