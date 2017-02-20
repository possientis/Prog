
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


# best to replace newline delimiter by null character with -print0 option
# then use xargs with -0 option. 

find . -name '*.sh' -print0 | xargs -0 file


