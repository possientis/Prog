FILE=/etc/passwd

read -p "Enter a user name > " user_name

file_info=$(grep "^$user_name:" $FILE)

# standard input redirected to string source with ' <<< my-string'
# <<< indicates a 'here string'
# note that you cannot pipe 'read'.... echo "foo" | read  won't work
# coz REPLY would be assigned a value in a subshell
if [ -n "$file_info" ]; then
  IFS=":" read user pw uid gid name home shell <<< "$file_info" 
  echo "User      = '$user'"
  echo "UID       = '$uid'"
  echo "GID       = '$gid'"
  echo "Full Name = '$name'"
  echo "Home Dir. = '$home'"
  echo "Shell     = '$shell'"
else
  echo "No such user '$user_name'" >&2
  exit 1
fi


