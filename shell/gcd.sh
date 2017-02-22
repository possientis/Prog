# argument check
ARGS=2
E_BADARGS=85

if [ $# -ne "$ARGS" ]
then
  echo "Usage: $(basename $0) first-number second-number" >&2
  exit $E_BADARGS
fi
# ------------------------------------------------------------


gcd ()
{
  dividend=$1
  divisor=$2
  remainder=1

  until [ "$remainder" -eq 0 ]
  do
    let "remainder = $dividend % $divisor"
    dividend=$divisor
    divisor=$remainder
  done
}


gcd $1 $2
echo "$dividend"
