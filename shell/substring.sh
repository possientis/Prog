stringZ=abcABC123ABCabc
#       |------|
#       12345678

echo `expr match "$stringZ" 'abc[A-Z]*.2'`  # 8   , regex
echo `expr "$stringZ" : 'abc[A-Z]*.2'`      # 8   , regex


echo `expr index "$stringZ" C12`            # 6
echo `expr index "$stringZ" 1c`             # 3   ????
# 'c' (in #3 position) matches before '1'.
