invalid_input () {
  echo "Invalid input '$REPLY'" >&2
  exit 1
}

read -p "Enter a single item > "

# input is empty (invalid)
[[ -z $REPLY ]] && invalid_input

# input is multiple items (invalid)
(( $(echo $REPLY | wc -w) > 1)) && invalid_input

# is input a valid file name?
if [[ $REPLY =~ ^[-[:alnum:]\._]+$ ]]; then
  echo "'$REPLY' is a valid filename."
else
  echo "The string '$REPLY' is not a valid file name"
fi

