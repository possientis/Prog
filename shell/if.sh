if ls &> /dev/null
then
  echo "ls command succeeded"
else
  echo "ls command failed"
fi

if xxx &> /dev/null
then
  echo "xxx command succeeded"
else
  echo "xxx command failed"
fi


echo "Testing \"0\""
if [ 0 ]
then
  echo "0 is true."
else
  echo "0 is false."
fi  # 0 is true.
echo

echo "Testing \"1\""
if [ 1 ]
then
  echo "1 is true."
else
  echo "1 is false."
fi  # 1 is true.
echo

echo "Testing \"-1\""
if [ -1 ]
then
  echo "-1 is true."
else
  echo "-1 is false."
fi  # -1 is true.
echo

echo "Testing \"NULL\""
if [ ]    # empty condition
then
  echo "NULL is true."
else
  echo "NULL is false."
fi  # NULL is false.
echo

echo "Testing \"\""
if [ "" ]    # empty string
then
  echo "\"\" is true."
else
  echo "\"\" is false."
fi  # "" is false.
echo

echo "Testing \"xyz\""
if [ xyz ]    # string
then
  echo "random string is true."
else
  echo "random string is false."
fi  # random string is true.
echo

echo "Testing \"\$xyz\""
if [ $xyz ]    # uninitialized variable
then
  echo "uninitialized variable is true."
else
  echo "uninitialized variable is false."
fi  # uninitialized variable is false.
echo

echo "Testing \"-n \$xyz\""
if [ -n "$xyz" ]
then
  echo "uninitialized variable is true."
else
  echo "uninitialized variable is false."
fi  # uninitialized variable is false.
echo

xyz=  # initialized, but set to null value
echo "Testing \"\$xyz\""
if [ $xyz ]
then
  echo "null value variable is true."
else
  echo "null value variable is false."
fi  # null value variable is false.
echo


echo "Testing \"-n \$xyz\""
if [ -n "$xyz" ]
then
  echo "null value variable is true."
else
  echo "null value variable is false."
fi  # null value variable is false.
echo


echo "Testing \"false\""
if [ "false" ]              # random string
then
  echo "\"false\" is true."
else
  echo "\"false\" is false."
fi  # "false" is true.
echo

echo "Testing \"\$false\""
if [ "$false" ]             # unitialized var
then
  echo "\"\$false\" is true."
else
  echo "\"\$false\" is false."
fi  # "\$false" is false.
echo









