MAIL=john@front
: ${HOSTNAME?} ${USER?} ${HOME?} ${MAIL?}

echo
echo "Name of the machine is $HOSTNAME."
echo "You are $USER."
echo "Your home directory is $HOME."
echo "Your mail INBOX is located in $MAIL."
echo
echo "If you are reading this message,"
echo "critical environmental variables have been set."
echo
echo

${NOT_DEFINED}      # fine
: ${NOT_DEFINED}    # still fine
: ${NOT_DEFINED?"This is my error message"}     # error

echo "script does not reach this point"

${NOT_DEFINED?}   # also an error
