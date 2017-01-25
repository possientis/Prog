# bash only

a=879
echo "The value of \"a\" is $a."

# assignment using 'let'
let a=16+5
echo "The value of \"a\" is now $a."

# in a 'for' loop
echo -n "Values of \"a\" in the loop are: "
for a in 7 8 9 11
do
  echo -n "$a "
done
echo


# in a 'read' statement
echo 1 2 3 4 > log      # simulating stdin
echo -n "Enter \"a\" "
read a < log            # avoiding stdin
echo
echo "The value of \"a\" is now $a." # The value of "a" is now 1 2 3 4.
rm log

# simple
a=23
echo "a = $a"
b=$a
echo "b = $b"

# fancy (command substitution)

# NOTE: exclamation mark (!) within a command substitution construct will not
# work from the command-line, since this triggers the bash "history mechanism"
# inside a script, however, the history functions are disabled by default

a=`echo Hello!` # assignes result of 'echo' command to 'a'
echo "a = $a" # a = Hello!

a=`ls -l`
echo $a     # very messy
echo "$a"   # preserves whitespace









