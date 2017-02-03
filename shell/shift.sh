# Using 'shift' to step through all the positional parameters

i=1

until [ -z "$1" ] # Until all parameters used up
do
  echo "Parameter $i is $1"
  shift           # or 'shift 1', can use 'shift 2', etc
  let  "i+=1"
done

echo
