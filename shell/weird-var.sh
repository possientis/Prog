echo

var="'(]\\{}\$\""
echo $var         # '(]\{}$"
echo "$var"       # '(]\{}$"  Doesn't make a difference

echo

IFS='\'           # special shell variable (internal field seperator)
echo $var         # '(] {}$"  \ converted to space, why? (no quotes, IFS -> space)
echo "$var"       # '(]\{}$"  quotes preserve IFS

echo 

var2="-\\\\\"-"
echo $var2        # -  "-  , no quotes, IFS character converted to space
echo "$var2"      # -\\"-  , quotes preserve IFS

# nesting quotes is permitted
echo

echo "$(echo '"')"  # "

var1="Two bits"
echo "\$var1 = "$var1"" # $var1 = Two bits

echo
IFS=' '
echo -n "short" > log1
echo -n "this is longer" > log2

my_file1=log1
my_file2=log2

rm log1 log2

echo "Why can't I write 's between single quotes"
echo
echo 'Why can'\''t I write '"'"'s between single quotes'
