
echo "The # here does not begin a comment."
echo 'The # here does not begin a comment.'
echo The \# here does not begin a comment.
echo The # here begins a comment.

echo ${PATH}          # normal path
echo ${PATH#*:}       # parameter substitution, not a comment
echo $(( 2#1010011 )) # base conversion, not a comment (= 83)

