echo

var="'(]\\{}\$\""
echo $var         # '(]\{}$"
echo "$var"       # '(]\{}$"  Doesn't make a difference

echo

IFS='\'           # special shell variable (internal field seperator)
echo $var         # '(] {}$"  \ converted to space, why? (no quote, IFS -> space)
echo "$var"       # '(]\{}$"  quotes preserve IFS

echo 

# TODO continue

