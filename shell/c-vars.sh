echo

(( a = 23 ))  #  setting a value, C-style with spaces on both sides of "=".
echo "a (initial value) = $a"

(( a++ ))     # post-increment 'a', C-style
echo "a (after a++) = $a"


(( a-- ))     # post-decrement 'a', C-style
echo "a (after a--) = $a"

(( ++a ))     # pre-increment 'a', C-style
echo "a (after ++a) = $a"


(( --a ))     # pre-decrement 'a', C-style
echo "a (after --a) = $a"

echo

########################################################
# Note that, as in C, pre- and post-decrement operators
#+ have different side-effects.
n=1; let --n && echo "True" || echo "False" # False (let 0 -> return status 1)
n=1; let n-- && echo "True" || echo "False" # True  (let 1 -> return status 0)
# 
########################################################

echo

(( t = a<45?7:11 ))   # C-style ternary operator
echo "t = $t" # 7


echo
