# Strips leading zero(s) from argument passed.

strip_leading_zero()
{
  return ${1#0}
}


strip_leading_zero 0123
var=$?  # how do i get the value returned by function???
echo "strip_leading_zero(0123)=${var}"

strip_leading_zero 00123
var=$?
echo "strip_leading_zero(00123)=${var}"


# Strip possible leading zero(s), since otherwise
# Bash will interpret such numbers as octal values.
strip_leading_zero2 () 
{
  shopt -s extglob      # Turn on extended globbing.
  local val=${1##+(0)}  # Use local variable, longest matching series of 0's.
  shopt -u extglob      # Turn off extended globbing.
  _strip_leading_zero2= #${val:-0} # If input was 0, return 0 instead of "".
}

strip_leading_zero 00
var=$?
echo $var


