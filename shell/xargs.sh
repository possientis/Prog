
# running the file command wih arguments equal
# to the output of "find . -name '*.sh'"

find . -name '*.sh' | xargs file    > log1
find . -name '*.sh' | file $(cat -) > log2 # achieves the same

if cmp log1 log2 &>/dev/null; then
  echo "The two commands have the same semantics"
else
  echo "The two commands have different semantics"
fi

rm -f log1 log2


