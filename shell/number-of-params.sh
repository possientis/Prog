word=1234567890abcdefgh
echo
echo ${#word}       # 18  (characters)

array=(1 2 3 4 5 6 7 8 9 0 a b c d e f g h)
echo
echo ${#array[@]}   # 18
echo ${#array[*]}   # 18

