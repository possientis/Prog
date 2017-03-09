getopt_simple()
{
  echo "getopt_simple()"
  echo "Parameters are '$*'"

  until [ -z "$1" ]
  do
    echo "Processing parameter of: '$1'"
    if [ ${1:0:1} = '/' ]
    then
      tmp=${1:1}  # Strip off leading '/' . . .
      parameter=${tmp%%=*} # Extract name.
      value=${tmp##*=}     # Extract value.
      echo "Parameter: '$parameter', value: '$value'"
      eval $parameter=$value
    fi
    shift
  done
}

getopt_simple $*

echo "test1 = '$test1'"
echo "test2 = '$test2'"
