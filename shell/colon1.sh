# only for bash
# gives an error without leading : colon
: ${username=`whoami`}
echo $username

: ${HOSTNAME?} ${USER?}
# gives an error if env variables not set

echo $HOSTNAME
echo $USER
