List="one two three"

for a in $List  #splits the variable in parts at whitespace
do
  echo "$a"
done

# one
# two
# three

echo "---"
for a in "$List"  # preserves whitespace in a single variable
do
  echo "$a"
done

# one two three

COMMAND=echo

variable1="a variable containing five words"
$COMMAND This is $variable1   # executes command with 7 arguments
$COMMAND "This is $variable1" # executes command with 1 argument

variable2=""  # empty
$COMMAND $variable2 $variable2 $variable2       # command with no argument
$COMMAND "$variable2" "$variable2" "$variable2" # command with 3 empty arguments
$COMMAND "$variable2 $variable2 $variable2"     # command with 1 argument (2space)



