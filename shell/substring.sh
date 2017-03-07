stringZ=abcABC123ABCabc
#       |------|
#       12345678

echo `expr match "$stringZ" 'abc[A-Z]*.2'`                  # 8   , regex
echo `expr "$stringZ" : 'abc[A-Z]*.2'`                      # 8   , regex


echo `expr index "$stringZ" C12`                            # 6
echo `expr index "$stringZ" 1c`                             # 3   ????
# 'c' (in #3 position) matches before '1'.


echo `expr substr $stringZ 1 2`                             # ab
echo `expr substr $stringZ 4 3`                             # ABC


echo `expr match "$stringZ" '\(abc[A-Z]*.2\)'`              # abcABC12, regex
echo `expr match "$stringZ" '\(.[b-c]*[A-Z]..[0-9]2\)'`     # abcABC12
echo `expr "$stringZ" : '\(.[b-c]*[A-Z]..[0-9]2\)'`         # abcABC12
echo `expr "$stringZ" : '\(........\)'`                     # abcABC12

echo `expr match "$stringZ" '.*\([A-C][A-C][A-C][a-c]*\)'`  # ABCabc
echo `expr "$stringZ" : '.*\(......\)'`                     # ABCabc, regex, longest match?


echo ${stringZ#a*C}                                         # 123ABCabc
# strips out shortest match between 'a' and 'C' (feels like globbing , not regex)


echo ${stringZ##a*C}                                        # abc
# strips out longest match between 'a' and 'C' (feels like globbing , not regex)

X='a*C'

echo ${stringZ#$X}                                          # 123ABCabc
echo ${stringZ##$X}                                         # abc



for i in $(ls)
do
  echo -n "${i%.sh} "    # $(basename $i .sh)
done
echo

echo ${stringZ%b*c}     # abcABC123ABCa
# strip out shortest match between 'b' and 'c' from back of stringZ


echo ${stringZ%%b*c}     # a
# strip out longest match between 'b' and 'c' from back of stringZ




