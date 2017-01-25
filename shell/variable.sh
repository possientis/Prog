# bash only (not everything works with sh)
# the semantics of variable substitution in weak quoting 

hello="A B  C   D"

# (weak) quoting a variable preserves white space
echo $hello       # A B C D
echo ${hello}     # A B C D
echo "$hello"     # A B  C   D
echo "${hello}"   # A B  C   D



hello=  # setting to null value
echo "\$hello (null value) = $hello"  # $hello (null value) = 

# uninitialized variable has null value
echo "uninitialized_variable = $uninitialized_variable"
uninitialized_variable= # still has null value
echo "uninitialized_variable = $uninitialized_variable"
uninitialized_variable=23 # set it
echo "uninitialized_variable = $uninitialized_variable"
unset uninitialized_variable  # unset it
echo "uninitialized_variable = $uninitialized_variable"

# null value is not the same as zero, but '-z' tests for null value
if [ -z "$unassigned" ]
then
  echo "\$unassigned is NULL."      # true
else
  echo "\$unassigned is not NULL."  # false
fi

unassigned=0
if [ -z "$unassigned" ]             
then
  echo "\$unassigned is NULL."      # false
else
  echo "\$unassigned is not NULL."  # true
fi

unassigned=
let "unassigned += 5" # add 5 to uninitialized variable still works
echo "\$unassigned = $unassigned"





var1=21 var2=22 var3=$v3
echo "var1=$var1  var2=$var2  var3=$var3"

# If there is whitespace embedded within a variable value
# then quotes are necessary
# other_number=1 2 3  # error
numbers="one two three"
other_numbers="1 2 3"

echo "numbers = $numbers"
echo "other_numbers = $other_numbers"

# escaping whitespace also works
mixed_bag=2\ ---\ Whatever
echo "$mixed_bag" # 2 --- Whatever


