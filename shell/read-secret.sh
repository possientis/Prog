if read -t 10 -sp "Enter secret pass phrase > " secret_pass; then
  echo -e "\nSecret pass phrase = '$secret_pass'"
else
  echo -e "\nInput timed out" >&2
  exit 1
fi
