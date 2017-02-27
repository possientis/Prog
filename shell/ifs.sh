var1="a+b+c"
var2="d-e-f"
var3="g,h,i"

IFS=+

# The plus sign will be interpreted as a separator.
echo $var1    # a b c
echo $var2    # d-e-f
echo $var3    # g,h,i

echo

IFS=-

# The minus sign will be interpreted as a separator.
echo $var1    # a+b+c
echo $var2    # d e f
echo $var3    # g,h,i

echo

IFS=,

# The comma will be interpreted as a separator.
echo $var1    # a+b+c
echo $var2    # d-e-f
echo $var3    # g h i

echo


IFS=" "
# The space character will be interpreted as a separator.
# The comma reverts to default interpretation.
echo $var1    # a+b+c
echo $var2    # d-e-f
echo $var3    # g,h,i

# ======================================================== #
# However ...
# $IFS treats whitespace differently than other characters.

output_args_one_per_line()
{
  for arg           # ... 'in $@' seems implicit here
  do
    echo "[$arg]"
  done  # ^    ^ Embed within brackets, for your viewing pleasure.
}




echo; echo "IFS=\" \""
echo "-------"
IFS=" "
var=" a  b   c"
#    ^ ^^ ^^^

output_args_one_per_line $var
# [a]
# [b]
# [c]


echo; echo "IFS=:"
echo "-----"
IFS=:
var=":a::b:c:::"
#    ^ ^^   ^^^

output_args_one_per_line $var
# []
# [a]
# []
# [b]
# [c]
# []
# []

echo 

exit









