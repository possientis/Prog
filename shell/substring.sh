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


echo ${stringZ/abc/xyz}         # xyzABC123ABCabc , replaces first match only
echo ${stringZ//abc/xyz}        # xyzABC123ABCxyz , replaces all matches
echo $stringZ                   # abcABC123ABCabc, string itself unaffected


# can match and replacement string be parameterized ?
match=abc
repl=xyz

echo ${stringZ/$match/$repl}    # xyzABC123ABCabc
echo ${stringZ//$match/$repl}   # xyzABC123ABCxyz

# What happens if no $replacement string is supplied?
echo ${stringZ/abc}             # ABC123ABCabc
echo ${stringZ//abc}            # ABC123ABC
# A simple deletion takes place.

echo ${stringZ/#abc/xyz}        # XYZABC123ABCabc
# Replaces front-end match of 'abc' with 'XYZ'.
echo ${stringZ/%abc/xyz}        # abcABC123ABCXYZ
# Replaces back-end match of 'abc' with 'XYZ'.



String=23skidoo1
#      012345678  Bash
#      123456789  awk

# Note different string indexing system:
# Bash numbers first character of string as 0.
# Awk numbers first character of string as 1.

echo ${String:2:4}    # position 3 (0-1-2), 4 characters long
                      # skid

# The awk equivalent of ${string:pos:length} is substr(string,pos,length).
echo | awk '
{ 
  print substr("'"${String}"'",3,4)   # skid
}
'
# Piping an empty "echo" to awk gives it dummy input,
#+ and thus makes it unnecessary to supply a filename.

echo "----"
# And likewise:
echo | awk '
{ 
  print index("'"${String}"'", "skid") # 3
} 
'  # (skid starts at position 3)

# The awk equivalent of "expr index" ...

exit 0


