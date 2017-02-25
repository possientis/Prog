echo "BASH=$BASH"


echo "BASH_ENV=$BASH_ENV"

echo "BASH_SUBSHELL=$BASH_SUBSHELL"

echo "BASHPID=$BASHPID"

echo "\$\$=$$"


# but ...

echo
echo "\$\$ outside of subshell = $$"
echo "BASH_SUBSHELL outside of subshell = $BASH_SUBSHELL"
echo "BASHPID outside of subshell = $BASHPID"

echo # Note that $$ returns PID of parent process.
( echo "\$\$ inside of subshell = $$"
  echo "\$BASH_SUBSHELL inside of subshell = $BASH_SUBSHELL"
  echo "\$BASHPID inside of subshell = $BASHPID" 
)

echo
# good way of checking which shell is running
echo "BASH_VERSION=$BASH_VERSION" # "" unless bash
echo "SHELL=$SHELL" # may not give the right answer (why?)

for n in 0 1 2 3 4 5
do
  echo "BASH_VERSINFO[$n]=${BASH_VERSINFO[$n]}"
done

echo
echo "CDPATH=$CDPATH"

echo 
echo "DIRSTACK=$DIRSTACK"

echo
echo "EDITOR=$EDITOR"

echo
echo "EUID=$EUID"


echo
xyz23 ()
{
  echo "$FUNCNAME now executing."
}
xyz23
echo "FUNCNAME=$FUNCNAME"

echo
echo "GLOBALIGNORE=$GLOBALIGNORE"

echo
echo "GROUPS=$GROUPS"
for n in 0 1 2 3 4 5 6 7 8 9 10 11 12 13  
do
  echo "GROUPS[$n]=${GROUPS[$n]}"
done


echo
echo "HOME=$HOME"

echo
echo "HOSTNAME=$HOSTNAME"

echo
echo "HOSTTYPE=$HOSTTYPE"
echo "MACHTYPE=$MACHTYPE"

echo
echo "|IFS|=|$IFS|"





