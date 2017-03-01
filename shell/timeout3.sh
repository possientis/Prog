TIMELIMIT=4 # 4 seconds

read -t $TIMELIMIT variable
echo
if [ -z "$variable" ] # Is null?
then
  echo "Timed out, variable still unset."
else
  echo "variable = $variable"
fi
exit 0
