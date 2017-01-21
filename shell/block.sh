# sh and bash
# block
a=123
{ a=321; }  # anonymous function but variable global
echo "a = $a" # a = 321

# redirecting standard input to a block

File=/etc/fstab
{
  read line1
  read line2
} < $File

echo "First line in $File is:"
echo "$line1"
echo
echo "Second line in $File is:"
echo "$line2"

# redirecting standard output from a block

{
  echo "This will not appear on stdout"
  echo "Since it is being redirected"
} > log

cat log; rm log

exit 0
